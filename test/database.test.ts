import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
import { describe, expect, it } from "vitest";
import { loadSubmissions } from "../src/database.js";
import { generateSite } from "../src/sitegen/generate.js";
import { tmpDir } from "./helpers.js";

describe("public database loader", () => {
  it("adapts accepted manifest and abstract inputs for the renderer", async () => {
    const database = tmpDir("lax-database-inputs-");
    const submission = path.join(database, "lax-14");
    fs.mkdirSync(submission);
    fs.writeFileSync(path.join(submission, "record.json"), JSON.stringify({
      specVersion: "1",
      id: "lax-14",
      state: "draft",
      createdAt: "2026-08-02T18:02:05Z",
      source: {
        repository: "https://github.com/example/submission",
        commit: "a".repeat(40),
        folder: ".",
      },
    }));
    fs.writeFileSync(path.join(submission, "build-output.json"), JSON.stringify({
      specVersion: "1",
      id: "lax-14",
      capture: {
        formatVersion: 1,
        digest: "d".repeat(64),
        sourceCommit: "a".repeat(40),
        leanToolchain: "leanprover/lean4:v4.30.0",
        mathlibCommit: "c".repeat(40),
        files: [],
      },
      inputs: {
        manifest: {
          specVersion: "1",
          id: "lax-14",
          leanVersion: "v4.30.0",
          mathlibVersion: "c".repeat(40),
          title: "Finite Ramsey Theorems",
          authors: [{ name: "Jan Dreier" }],
          bibEntries: [],
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
    expect(submissions[0]?.output?.abstract).toBe("A validated abstract.");

    const site = tmpDir("lax-site-inputs-");
    await generateSite(submissions, site);
    expect(fs.readFileSync(path.join(site, "index.html"), "utf8")).toContain(
      "Finite Ramsey Theorems",
    );
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
      capture: {
        formatVersion: 1,
        digest: "d".repeat(64),
        sourceCommit: "a".repeat(40),
        leanToolchain: "leanprover/lean4:v4.30.0",
        mathlibCommit: "c".repeat(40),
        files: [],
      },
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

  it("binds rendered sources and links to the pinned validation capture", async () => {
    const database = tmpDir("lax-database-integrity-");
    const submission = path.join(database, "lax-18");
    fs.mkdirSync(submission);
    const sourceText = "namespace Lax18.C\naxiom truth : True\nend Lax18.C\n";
    const sourceHash = createHash("sha256").update(sourceText).digest("hex");
    const record = {
      specVersion: "1", id: "lax-18", state: "registered", createdAt: "2026-08-02T18:18:08Z",
      source: { repository: "https://github.com/example/submission", commit: "a".repeat(40), folder: "." },
    };
    const output = {
      specVersion: "1", id: "lax-18",
      capture: {
        formatVersion: 1, digest: "d".repeat(64), sourceCommit: "a".repeat(40),
        leanToolchain: "leanprover/lean4:v4.30.0", mathlibCommit: "c".repeat(40),
        files: [{ path: "concepts/package/Lax18/C.lean", bytes: Buffer.byteLength(sourceText), sha256: sourceHash }],
      },
      inputs: {
        manifest: { specVersion: "1", id: "lax-18", leanVersion: "v4.30.0", mathlibVersion: "c".repeat(40), title: "Captured", authors: [], bibEntries: [] },
        abstract: "Checked.",
      },
      requiredByConcepts: [], requiredByProofs: [],
      concepts: [{ id: "Lax18.C", path: "concepts/Lax18/C.lean", title: "Truth", type: "theorem", description: "True.", imports: [], sourceText, statements: [{ id: "Lax18.C.truth", signature: "truth : True" }] }],
      proofs: [],
    };
    fs.writeFileSync(path.join(submission, "record.json"), JSON.stringify(record));
    fs.writeFileSync(path.join(submission, "build-output.json"), JSON.stringify(output));

    const submissions = loadSubmissions(database);
    expect(submissions[0]?.integrity?.conceptFiles["Lax18.C"]?.sha256).toBe(sourceHash);
    const site = tmpDir("lax-site-integrity-");
    await generateSite(submissions, site);
    const index = fs.readFileSync(path.join(site, "index.html"), "utf8");
    const concept = fs.readFileSync(path.join(site, "lax-18", "Lax18.C.html"), "utf8");
    expect(index).toMatch(/href="lax-18\/index\.html\?v=[0-9a-f]{16}"/);
    expect(concept).toContain(`Archived source SHA-256 <code>${sourceHash}</code>`);
    expect(concept).toContain(`validation capture <code>sha256:${"d".repeat(64)}</code>`);

    const badCommit = { ...output, capture: { ...output.capture, sourceCommit: "b".repeat(40) } };
    fs.writeFileSync(path.join(submission, "build-output.json"), JSON.stringify(badCommit));
    expect(() => loadSubmissions(database)).toThrow("capture commit");

    const badSource = { ...output, concepts: [{ ...output.concepts[0]!, sourceText: `${sourceText}\n-- stale` }] };
    fs.writeFileSync(path.join(submission, "build-output.json"), JSON.stringify(badSource));
    expect(() => loadSubmissions(database)).toThrow("does not match capture file");
  });
});
