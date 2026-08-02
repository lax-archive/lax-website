import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { loadSubmissions } from "../src/database.js";
import { generateSite } from "../src/sitegen/generate.js";
import { tmpDir } from "./helpers.js";

describe("public database loader", () => {
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
});
