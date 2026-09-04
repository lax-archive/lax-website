import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { EPOCH } from "../src/config.js";
import { generateSite, type SiteSubmission } from "../src/sitegen/generate.js";
import { environmentIndex, recordIndex } from "../src/sitegen/machine-index.js";
import { SiteModel } from "../src/sitegen/model.js";
import { tmpDir } from "./helpers.js";

/** A record in one environment. `state` and `supersedes` cover the two facts
 * the listings and the index files order and link by. */
function make(
  id: string,
  environment: string,
  state: "registered" | "draft" = "registered",
  supersedes?: string,
): SiteSubmission {
  const pkg = id.replace(/\W/g, "");
  return {
    record: {
      specVersion: "1", id, state, createdAt: "2026-01-01T00:00:00Z",
      ...(state === "registered" ? { registeredAt: "2026-01-02T00:00:00Z" } : {}),
      source: { repository: "https://github.com/example/math", commit: "a".repeat(40), folder: "." },
    },
    output: {
      specVersion: "1", id,
      manifest: {
        specVersion: "1", id, leanVersion: environment, mathlibVersion: `mathlib-${environment}`,
        title: `Result ${id}`, authors: [], bibEntries: [], ...(supersedes ? { supersedes } : {}),
      },
      abstract: "An abstract.", requiredByConcepts: [], requiredByProofs: [],
      concepts: [{
        id: `${pkg}.C`, path: "concepts/C.lean", title: "A concept", type: "definition",
        description: "d", imports: [], mathlibImports: [], sourceText: "-- lean\n",
        statements: [{ id: `${pkg}.C.claim`, signature: "claim : True" }],
      }],
      proofs: [{
        id: `${pkg}Proofs.claim`, path: "proofs/Claim.lean", conclusion: `${pkg}.C.claim`,
        assumptions: [], description: "The proof.",
      }],
    },
  };
}

/** Three environments, one of them the epoch, plus a version chain that
 * crosses from the epoch into a newer environment — the shape a port makes. */
function archive(): SiteSubmission[] {
  return [
    make("lax-1", "v4.30.0"),
    make("lax-2", "v4.33.0"),
    make("lax-3", "v4.31.0"),
    make("lax-4", "v4.30.0", "draft"),
    // lax-5 ports lax-1 into v4.33.0, so lax-1 leaves the listings.
    make("lax-5", "v4.33.0", "registered", "lax-1"),
  ];
}

/** Row order of the landing page's library, by archive id. */
const listed = (html: string): string[] => {
  const library = html.slice(html.indexOf('<ul class="submissions-list" id="submissions-list">'));
  return [...library.matchAll(/<li data-search-title="([a-z0-9-]+) /g)].map((match) => match[1]!);
};

describe("archive environments on the site", () => {
  it("says which environment an off-epoch record is in, and only then", async () => {
    const root = tmpDir("lax-site-env-notice-");
    await generateSite(archive(), root, "v4.30.0");

    const off = fs.readFileSync(path.join(root, "lax-2", "index.html"), "utf8");
    expect(off).toContain(
      '<p class="environment-notice">Environment <code>v4.33.0</code>. '
      + "The archive's epoch is <code>v4.30.0</code>; "
      + "only submissions in <code>v4.33.0</code> can cite this work.</p>",
    );
    // the same notice on every page of that submission
    for (const page of ["lax2.C.html", "lax2Proofs.claim.html"])
      expect(fs.readFileSync(path.join(root, "lax-2", page), "utf8")).toContain('class="environment-notice"');
    // no warning palette, no icon: it is a fact about citation, not a fault
    expect(off).not.toContain("environment-notice warn");

    const epoch = fs.readFileSync(path.join(root, "lax-4", "index.html"), "utf8");
    expect(epoch).not.toContain("environment-notice");
    expect(epoch).toContain('class="draft-banner"');
    expect(epoch).toContain('<span class="meta-epoch"');
    expect(off).not.toContain('<span class="meta-epoch"');
  });

  it("keeps the version dialog's per-version pins across an environment port", async () => {
    const root = tmpDir("lax-site-env-chain-");
    await generateSite(archive(), root, "v4.30.0");

    const ported = fs.readFileSync(path.join(root, "lax-5", "index.html"), "utf8");
    expect(ported).toContain("Lean</b> <code>v4.30.0</code>");
    expect(ported).toContain("Lean</b> <code>v4.33.0</code>");
    expect(ported).toContain("mathlib</b> <code>mathlib-v4.30.0</code>");
    expect(ported).toContain("mathlib</b> <code>mathlib-v4.33.0</code>");
    // the predecessor is in the epoch and still says nothing; its successor,
    // which readers are sent to, is the one that names its island
    expect(fs.readFileSync(path.join(root, "lax-1", "index.html"), "utf8"))
      .not.toContain("environment-notice");
    expect(ported).toContain('class="environment-notice"');
  });

  it("orders listings by environment and offers them as chips", async () => {
    const root = tmpDir("lax-site-env-order-");
    await generateSite(archive(), root, "v4.30.0");
    const html = fs.readFileSync(path.join(root, "index.html"), "utf8");

    // registered before drafts; inside each, the epoch first and the other
    // environments newest first (v4.33.0 before v4.31.0), archive ids last.
    // lax-1 is superseded by its port and drops out of the listing entirely.
    expect(listed(html)).toEqual(["lax-2", "lax-5", "lax-3", "lax-4"]);
    // the sidebar is generated from the same order
    const sidebar = html.slice(0, html.indexOf('<ul class="submissions-list"'));
    expect([...sidebar.matchAll(/<li data-search-title="([a-z0-9-]+) /g)].map((m) => m[1]!))
      .toEqual(["lax-2", "lax-5", "lax-3", "lax-4"]);
  });

  it("carries the environment as a row attribute and a chip filter key", async () => {
    const root = tmpDir("lax-site-env-facet-");
    await generateSite(archive(), root, "v4.30.0");
    const html = fs.readFileSync(path.join(root, "index.html"), "utf8");

    expect(html).toContain('data-env="v4.33.0"');
    expect(html).toMatch(/data-env="v4\.33\.0" data-search-order="\d+" data-tags="[^"]*\|v4\.33\.0\|"/);
    expect(html).toContain('data-tag-filter="v4.30.0"');
    expect(html).toContain("<span>v4.30.0 · epoch</span>");
    expect(html).toContain('data-tag-filter="v4.33.0"');
    expect(html).toContain("Environments first, then topics");

    // one environment, no chips: the only chip there could be names the only
    // thing there is
    const single = tmpDir("lax-site-env-single-");
    await generateSite([make("lax-1", "v4.30.0")], single, "v4.30.0");
    const only = fs.readFileSync(path.join(single, "index.html"), "utf8");
    expect(only).not.toContain('data-tag-filter="v4.30.0"');
    expect(only).toContain('data-env="v4.30.0"');
    expect(only).toContain("Suggested from submission and concept titles.");
  });

  it("takes the epoch as the third argument and falls back to the config", async () => {
    const submissions = [make("lax-1", "v4.30.0"), make("lax-2", "v4.33.0")];

    const moved = tmpDir("lax-site-env-arg-");
    await generateSite(submissions, moved, "v4.33.0");
    expect(fs.readFileSync(path.join(moved, "lax-1", "index.html"), "utf8"))
      .toContain("The archive's epoch is <code>v4.33.0</code>");
    expect(fs.readFileSync(path.join(moved, "lax-2", "index.html"), "utf8"))
      .not.toContain("environment-notice");
    expect(JSON.parse(fs.readFileSync(path.join(moved, "environments.json"), "utf8")).epoch)
      .toBe("v4.33.0");

    // the same value in the options bag, and nothing at all
    const bag = tmpDir("lax-site-env-bag-");
    await generateSite(submissions, bag, { epoch: "v4.33.0" });
    expect(fs.readFileSync(path.join(bag, "environments.json"), "utf8"))
      .toBe(fs.readFileSync(path.join(moved, "environments.json"), "utf8"));

    const configured = tmpDir("lax-site-env-config-");
    await generateSite(submissions, configured, {});
    expect(JSON.parse(fs.readFileSync(path.join(configured, "environments.json"), "utf8")).epoch)
      .toBe(EPOCH);
  });

  it("writes a machine-readable record index and environment index", async () => {
    const root = tmpDir("lax-site-env-json-");
    await generateSite(archive(), root, "v4.30.0");

    const index = JSON.parse(fs.readFileSync(path.join(root, "index.json"), "utf8")) as
      { records: Array<Record<string, unknown>> };
    expect(index.records.map((record) => record.id)).toEqual(["lax-1", "lax-2", "lax-3", "lax-4", "lax-5"]);
    expect(index.records[0]).toEqual({
      id: "lax-1",
      state: "registered",
      environment: "v4.30.0",
      title: "Result lax-1",
      supersededBy: "lax-5",
      concepts: [{ id: "lax1.C", title: "A concept", type: "definition" }],
      proofs: ["lax1Proofs.claim"],
    });
    expect(index.records[4]).toMatchObject({ id: "lax-5", supersedes: "lax-1", environment: "v4.33.0" });
    // absent version links are absent keys, not nulls
    expect(Object.keys(index.records[1]!)).toEqual([
      "id", "state", "environment", "title", "concepts", "proofs",
    ]);

    const environments = JSON.parse(fs.readFileSync(path.join(root, "environments.json"), "utf8")) as unknown;
    expect(environments).toEqual({
      epoch: "v4.30.0",
      environments: [
        { id: "v4.30.0", registered: 1, drafts: 1 },
        { id: "v4.33.0", registered: 2, drafts: 0 },
        { id: "v4.31.0", registered: 1, drafts: 0 },
      ],
    });
    // the epoch is listed even with nothing in it: it answers "where do I
    // submit", which is not a count
    expect(environmentIndex(new SiteModel([make("lax-1", "v4.33.0")], "v4.30.0")).environments)
      .toEqual([
        { id: "v4.30.0", registered: 0, drafts: 0 },
        { id: "v4.33.0", registered: 1, drafts: 0 },
      ]);
  });

  it("emits both index files byte-identically on a rebuild", async () => {
    const first = tmpDir("lax-site-env-repeat-a-");
    const second = tmpDir("lax-site-env-repeat-b-");
    await generateSite(archive(), first, "v4.30.0");
    await generateSite([...archive()].reverse(), second, "v4.30.0");
    for (const name of ["index.json", "environments.json"]) {
      expect(fs.readFileSync(path.join(second, name), "utf8"))
        .toBe(fs.readFileSync(path.join(first, name), "utf8"));
    }
    // and the shapes come out of the model the same way the files did
    const model = new SiteModel(archive(), "v4.30.0");
    expect(`${JSON.stringify(recordIndex(model), null, 2)}\n`)
      .toBe(fs.readFileSync(path.join(first, "index.json"), "utf8"));
  });

  it("ignores records that only reserved an id", () => {
    const model = new SiteModel([
      make("lax-1", "v4.33.0"),
      { record: { specVersion: "1", id: "lax-9", state: "init", createdAt: "2026-01-01T00:00:00Z" } },
    ], "v4.30.0");
    expect(model.environments).toEqual(["v4.33.0"]);
    expect(recordIndex(model).records.map((record) => record.id)).toEqual(["lax-1"]);
    expect(environmentIndex(model).environments).toEqual([
      { id: "v4.30.0", registered: 0, drafts: 0 },
      { id: "v4.33.0", registered: 1, drafts: 0 },
    ]);
  });
});
