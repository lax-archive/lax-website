import fs from "node:fs";
import path from "node:path";
import { describe, expect, it, vi } from "vitest";
import { loadSubmissions } from "../src/database.js";
import { generateSite } from "../src/sitegen/generate.js";
import { tmpDir } from "./helpers.js";

describe("public database loader", () => {
  it("adapts accepted manifest and abstract inputs, including presentation flags", async () => {
    const database = tmpDir("lax-database-inputs-");
    const submission = path.join(database, "lax-14");
    fs.mkdirSync(submission);
    fs.writeFileSync(path.join(submission, "record.json"), JSON.stringify({
      specVersion: "1",
      id: "lax-14",
      state: "draft",
      createdAt: "2026-08-02T18:02:05Z",
    }));
    fs.writeFileSync(path.join(submission, "build-output.json"), JSON.stringify({
      specVersion: "1",
      id: "lax-14",
      inputs: {
        manifest: {
          specVersion: "1",
          id: "lax-14",
          leanVersion: "v4.30.0",
          mathlibVersion: "c".repeat(40),
          title: "Finite Ramsey Theorems",
          authors: [{ name: "Jan Dreier" }],
          bibEntries: [],
          unlisted: true,
          anonymous: true,
        },
        abstract: "A validated abstract.",
      },
      requiredByConcepts: [],
      requiredByProofs: [],
      concepts: [],
      proofs: [],
    }));

    const submissions = loadSubmissions(database);
    expect(submissions[0]?.output?.manifest.title).toBe("Finite Ramsey Theorems");
    expect(submissions[0]?.output?.manifest.unlisted).toBe(true);
    expect(submissions[0]?.output?.manifest.anonymous).toBe(true);
    expect(submissions[0]?.output?.abstract).toBe("A validated abstract.");

    const site = tmpDir("lax-site-inputs-");
    await generateSite(submissions, site);
    expect(fs.readFileSync(path.join(site, "index.html"), "utf8")).not.toContain("Finite Ramsey Theorems");
    const direct = fs.readFileSync(path.join(site, "lax-14", "index.html"), "utf8");
    expect(direct).toContain("Finite Ramsey Theorems");
    expect(direct).toContain("withheld during anonymous review");
    expect(direct).not.toContain("Jan Dreier");
  });

  it("omits the byline when the manifest author list is empty", async () => {
    const database = tmpDir("lax-database-empty-authors-");
    const submission = path.join(database, "lax-16");
    fs.mkdirSync(submission);
    fs.writeFileSync(path.join(submission, "record.json"), JSON.stringify({
      specVersion: "1",
      id: "lax-16",
      state: "draft",
      createdAt: "2026-08-02T18:18:08Z",
      source: {
        repository: "https://github.com/example/submission",
        commit: "a".repeat(40),
        folder: "submission",
      },
    }));
    fs.writeFileSync(path.join(submission, "build-output.json"), JSON.stringify({
      specVersion: "1",
      id: "lax-16",
      inputs: {
        manifest: {
          specVersion: "1",
          id: "lax-16",
          leanVersion: "v4.30.0",
          mathlibVersion: "c".repeat(40),
          title: "An Authorless Submission",
          authors: [],
          bibEntries: [],
        },
        abstract: "A validated abstract.",
      },
      requiredByConcepts: [],
      requiredByProofs: [],
      concepts: [],
      proofs: [],
    }));

    const site = tmpDir("lax-site-empty-authors-");
    await generateSite(loadSubmissions(database), site);
    const html = fs.readFileSync(path.join(site, "lax-16", "index.html"), "utf8");
    expect(html).toContain("An Authorless Submission");
    expect(html).not.toContain('class="paper-authors"');
    expect(html).not.toContain("formalized by");
  });

  it("ignores init records without reading or rendering their build-output stubs", async () => {
    const database = tmpDir("lax-database-init-");
    const submission = path.join(database, "lax-3");
    fs.mkdirSync(submission);
    fs.writeFileSync(path.join(submission, "record.json"), JSON.stringify({
      specVersion: "1",
      id: "lax-3",
      state: "init",
      createdAt: "2026-08-02T16:22:39Z",
    }));
    // A rebuild must not inspect an init record's non-renderable provenance
    // stub. Invalid JSON makes that boundary explicit in this regression test.
    fs.writeFileSync(path.join(submission, "build-output.json"), "not renderable JSON");

    const submissions = loadSubmissions(database);
    expect(submissions).toEqual([]);

    const site = tmpDir("lax-site-init-");
    await generateSite(submissions, site);
    expect(fs.existsSync(path.join(site, "lax-3"))).toBe(false);
  });

  it("skips a record it cannot parse, names it, and loads the rest", () => {
    // One malformed record must not stall every later rebuild: the loader
    // reports it and goes on, and the site is built from what parsed.
    const database = tmpDir("lax-database-skip-");
    const write = (id: string, record: string, output?: string) => {
      fs.mkdirSync(path.join(database, id));
      fs.writeFileSync(path.join(database, id, "record.json"), record);
      if (output !== undefined) fs.writeFileSync(path.join(database, id, "build-output.json"), output);
    };
    write("lax-1", JSON.stringify({ specVersion: "1", id: "lax-1", state: "draft", createdAt: "2026-08-02T18:02:05Z" }));
    write("lax-2", "{ not json");
    write("lax-4", JSON.stringify({ specVersion: "1", id: "lax-4", state: "registered", createdAt: "2026-08-02T18:02:05Z" }),
      JSON.stringify({ specVersion: "1", id: "lax-4", manifest: {}, abstract: "x", requiredByConcepts: [], requiredByProofs: [], concepts: "no", proofs: [] }));
    write("lax-5", JSON.stringify({ specVersion: "1", id: "lax-9", state: "registered", createdAt: "2026-08-02T18:02:05Z" }));
    const skipped: Array<{ id: string; reason: string }> = [];

    const submissions = loadSubmissions(database, { onSkip: (skip) => skipped.push(skip) });

    expect(submissions.map((submission) => submission.record.id)).toEqual(["lax-1"]);
    expect(skipped.map((skip) => skip.id)).toEqual(["lax-2", "lax-4", "lax-5"]);
    expect(skipped[0]!.reason).toMatch(/JSON/u);
    expect(skipped[1]!.reason).toContain("concepts must be an array");
    expect(skipped[2]!.reason).toContain('names "lax-9", not lax-5');
  });

  it("never skips silently: without a callback the skip is a console warning", () => {
    const database = tmpDir("lax-database-skip-warn-");
    fs.mkdirSync(path.join(database, "lax-2"));
    fs.writeFileSync(path.join(database, "lax-2", "record.json"), "{ not json");
    const warn = vi.spyOn(console, "warn").mockImplementation(() => undefined);
    try {
      expect(loadSubmissions(database)).toEqual([]);
      expect(warn).toHaveBeenCalledTimes(1);
      expect(warn.mock.calls[0]![0]).toMatch(/^skipping lax-2: /u);
    } finally {
      warn.mockRestore();
    }
  });
});
