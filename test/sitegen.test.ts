import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { SITE_MIME, siteAssetPath } from "../src/sitegen/assets.js";
import { generateSite, type SiteSubmission } from "../src/sitegen/generate.js";
import { countsPill, statePill, typeBadge, typeBadgeText } from "../src/sitegen/html.js";
import { compareIds, SiteModel } from "../src/sitegen/model.js";
import { MarkdownRenderer } from "../src/sitegen/markdown.js";
import { ordinal, repositorySource, sourceProviderName, statementOrdinal } from "../src/sitegen/pages/shared.js";
import { submissionTagIndex } from "../src/sitegen/tags.js";
import { tmpDir } from "./helpers.js";

const submissions = (): SiteSubmission[] => [{
  record: {
    specVersion: "1", id: "Lax2", state: "registered", createdAt: "2026-01-01T00:00:00Z",
    registeredAt: "2026-01-02T00:00:00Z",
    source: { repository: "https://github.com/example/math.git", commit: "a".repeat(40), folder: "." },
  },
  output: {
    specVersion: "1", id: "Lax2",
    manifest: { specVersion: "1", id: "Lax2", leanVersion: "v4.30.0", mathlibVersion: "abc", title: "Two", authors: [{ name: "Alice", github: "alice", orcid: "0000-0002-1825-0097" }], bibEntries: ["@article{demo,\n  author = {Doe, Jane and M{\\\"u}ller, Hans},\n  title = {A Cited Result},\n  journal = {J. Math},\n  volume = {1},\n  number = {2},\n  pages = {3--4},\n  year = {2020},\n  doi = {10.1000/demo},\n}", "@book{x}"] },
    abstract: "See [[Lax2.C]], [[Lax2.C.truth|the statement]], and $x^2$. Broken: [[Nobody]].",
    requiredByConcepts: [], requiredByProofs: [],
    concepts: [
      {
        id: "Lax2.C", path: "concepts/Lax2/C.lean", title: "Truth", type: "theorem",
        description: "A description with $$x+y$$.",
        sections: [{ title: "Review notes", markdown: "Looks fine." }],
        imports: [], mathlibImports: ["Mathlib.Data.Nat.Basic"],
        sourceText: "namespace Lax2.C\n/-- True. -/\naxiom truth : True\nend Lax2.C",
        statements: [{ id: "Lax2.C.truth", signature: "truth : True", startLine: 2, endLine: 3, doc: "A true statement." }],
      },
      {
        id: "Lax2.D", path: "concepts/Lax2/D.lean", title: "Definition helper", type: "definition",
        description: "No statements here.", imports: ["Lax2.C"], mathlibImports: [],
        sourceText: "import Lax2.C\n", statements: [],
      },
    ],
    proofs: [{ id: "Lax2Proofs.truth", path: "proofs/Lax2Proofs/Basic.lean", conclusion: "Lax2.C.truth", assumptions: [], description: "The direct proof.", sections: [{ title: "Strategy", markdown: "Trivial." }] }],
  },
}, {
  record: { specVersion: "1", id: "Lax10", state: "init", createdAt: "2026-01-03T00:00:00Z" },
}];

/** The landing page's demonstration submission, cut down to the two
 * concepts its paper excerpt marks (marks 2 and 3, after the submission
 * mark) and the proof of the second. */
function introSubmission(): SiteSubmission {
  const point = (page: number, y: number) => ({ page, x: 125.8, y, mode: "v" as const });
  return {
    record: {
      specVersion: "1", id: "lax-242665", state: "draft", createdAt: "2026-09-07T16:18:55Z",
      source: { repository: "https://github.com/lax-archive/lax-submissions", commit: "b".repeat(40), folder: "lax-introduction" },
    },
    output: {
      specVersion: "1", id: "lax-242665",
      manifest: { specVersion: "1", id: "lax-242665", leanVersion: "v4.30.0", mathlibVersion: "abc", title: "An Introduction to Lax", authors: [{ name: "Jan Dreier" }], bibEntries: [] },
      abstract: "An introduction to Lax, written as a Lax submission.",
      requiredByConcepts: [], requiredByProofs: [],
      concepts: [
        {
          id: "Lax242665.Primes", path: "concepts/Lax242665/Primes.lean", title: "Prime numbers", type: "definition",
          description: "A natural number greater than 1 is *prime* if it is divisible only by 1 and by itself.",
          imports: [], mathlibImports: ["Mathlib.Data.Nat.Notation"],
          sourceText: "namespace Lax242665.Primes\ndef Prime (n : ℕ) : Prop :=\n  1 < n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n\nend Lax242665.Primes\n",
          statements: [],
        },
        {
          id: "Lax242665.InfinitelyManyPrimes", path: "concepts/Lax242665/InfinitelyManyPrimes.lean", title: "There are infinitely many primes", type: "theorem",
          description: "For every natural number $n$ there is a prime number $p > n$.",
          imports: ["Lax242665.Primes"], mathlibImports: [],
          sourceText: "namespace Lax242665.InfinitelyManyPrimes\naxiom exists_prime_gt (n : ℕ) : ∃ p, n < p ∧ Primes.Prime p\nend Lax242665.InfinitelyManyPrimes\n",
          statements: [{ id: "Lax242665.InfinitelyManyPrimes.exists_prime_gt", signature: "exists_prime_gt (n : ℕ) : ∃ p, n < p ∧ Primes.Prime p", startLine: 2, endLine: 2, doc: "Beyond every natural number lies a prime." }],
        },
        {
          id: "Lax242665.OddPrimes", path: "concepts/Lax242665/OddPrimes.lean", title: "Every prime other than 2 is odd", type: "lemma",
          description: "Every prime number $p \\neq 2$ is odd.", imports: ["Lax242665.Primes"], mathlibImports: [],
          sourceText: "namespace Lax242665.OddPrimes\naxiom odd_of_prime (p : ℕ) (hp : Primes.Prime p) (h2 : p ≠ 2) : Odd p\nend Lax242665.OddPrimes\n",
          statements: [{ id: "Lax242665.OddPrimes.odd_of_prime", signature: "odd_of_prime (p : ℕ) (hp : Primes.Prime p) (h2 : p ≠ 2) : Odd p", startLine: 2, endLine: 2, doc: "A prime other than 2 is odd." }],
        },
        {
          id: "Lax242665.BertrandPostulate", path: "concepts/Lax242665/BertrandPostulate.lean", title: "Bertrand's postulate", type: "lemma",
          description: "For every natural number $n \\geq 1$ there is a prime number $p$ with $n < p \\leq 2n$.", imports: ["Lax242665.Primes"], mathlibImports: [],
          sourceText: "namespace Lax242665.BertrandPostulate\naxiom exists_prime_between (n : ℕ) (hn : 1 ≤ n) : ∃ p, Primes.Prime p ∧ n < p ∧ p ≤ 2 * n\nend Lax242665.BertrandPostulate\n",
          statements: [{ id: "Lax242665.BertrandPostulate.exists_prime_between", signature: "exists_prime_between (n : ℕ) (hn : 1 ≤ n) : ∃ p, Primes.Prime p ∧ n < p ∧ p ≤ 2 * n", startLine: 2, endLine: 2, doc: "Between n and 2n there is always a prime." }],
        },
        {
          id: "Lax242665.OddPrimeBetween", path: "concepts/Lax242665/OddPrimeBetween.lean", title: "An odd prime between n and 2n", type: "theorem",
          description: "For every natural number $n \\geq 2$ there is an odd prime number $p$ with $n < p \\leq 2n$.", imports: ["Lax242665.Primes"], mathlibImports: [],
          sourceText: "namespace Lax242665.OddPrimeBetween\naxiom exists_odd_prime_between (n : ℕ) (hn : 2 ≤ n) : ∃ p, Primes.Prime p ∧ Odd p ∧ n < p ∧ p ≤ 2 * n\nend Lax242665.OddPrimeBetween\n",
          statements: [{ id: "Lax242665.OddPrimeBetween.exists_odd_prime_between", signature: "exists_odd_prime_between (n : ℕ) (hn : 2 ≤ n) : ∃ p, Primes.Prime p ∧ Odd p ∧ n < p ∧ p ≤ 2 * n", startLine: 2, endLine: 2, doc: "Between n ≥ 2 and 2n there is always an odd prime." }],
        },
      ],
      proofs: [
        {
          id: "Lax242665Proofs.InfinitelyManyPrimes.exists_prime_gt", path: "proofs/Lax242665Proofs/InfinitelyManyPrimes.lean",
          conclusion: "Lax242665.InfinitelyManyPrimes.exists_prime_gt", assumptions: [], description: "Euclid's argument.",
        },
        {
          id: "Lax242665Proofs.OddPrimes.odd_of_prime", path: "proofs/Lax242665Proofs/OddPrimes.lean",
          conclusion: "Lax242665.OddPrimes.odd_of_prime", assumptions: [], description: "An even prime is divisible by 2.",
        },
        {
          id: "Lax242665Proofs.OddPrimeBetween.exists_odd_prime_between", path: "proofs/Lax242665Proofs/OddPrimeBetween.lean",
          conclusion: "Lax242665.OddPrimeBetween.exists_odd_prime_between",
          assumptions: ["Lax242665.BertrandPostulate.exists_prime_between", "Lax242665.OddPrimes.odd_of_prime"],
          description: "Bertrand's postulate gives a prime, which is odd since it is not 2.",
        },
      ],
      paper: {
        folder: "paper", main: "main.tex", engine: "pdflatex",
        pdf: { digest: "c".repeat(64), bytes: 1, pages: 5, registryBlob: `ghcr.io/lax-archive/lax-captures@sha256:${"c".repeat(64)}` },
        pageSizes: [[612, 792], [612, 792], [612, 792], [612, 792], [612, 792]],
        marks: [
          { id: "lax-242665", kind: "submission", begin: point(1, 518.21), end: { page: 1, x: 218.11, y: 422.57, mode: "h" } },
          { id: "Lax242665.Primes", kind: "concept", begin: point(1, 321.07), end: point(1, 285.01) },
          { id: "Lax242665.InfinitelyManyPrimes", kind: "concept", begin: point(1, 285.01), end: point(1, 261.89) },
          { id: "Lax242665Proofs.InfinitelyManyPrimes.exists_prime_gt", kind: "proof", begin: point(2, 441.89), end: point(2, 392.82) },
          { id: "Lax242665.OddPrimes", kind: "concept", begin: point(2, 200), end: point(2, 180) },
          { id: "Lax242665Proofs.OddPrimes.odd_of_prime", kind: "proof", begin: point(2, 180), end: point(3, 700) },
          { id: "Lax242665.BertrandPostulate", kind: "concept", begin: point(3, 680), end: point(3, 650) },
          { id: "Lax242665.OddPrimeBetween", kind: "concept", begin: point(3, 650), end: point(3, 620) },
          { id: "Lax242665Proofs.OddPrimeBetween.exists_odd_prime_between", kind: "proof", begin: point(3, 620), end: point(3, 580) },
        ],
      },
    },
  };
}

function graphSubmissions(): SiteSubmission[] {
  const make = (
    id: string,
    concepts: { conceptId: string; imports: string[]; statements?: { id: string; signature: string }[] }[],
    proofs: NonNullable<SiteSubmission["output"]>["proofs"] = [],
  ): SiteSubmission => ({
    record: { specVersion: "1", id, state: "registered", createdAt: "2026-01-01T00:00:00Z" },
    output: {
      specVersion: "1", id,
      manifest: { specVersion: "1", id, leanVersion: "v4.30.0", mathlibVersion: "abc", title: id, authors: [], bibEntries: [] },
      abstract: "", requiredByConcepts: [], requiredByProofs: [],
      concepts: concepts.map(({ conceptId, imports, statements }) => ({
        id: conceptId, path: `concepts/${conceptId.replaceAll(".", "/")}.lean`, title: conceptId,
        type: statements?.length ? "theorem" : "definition",
        description: "", imports, mathlibImports: [], sourceText: "", statements: statements ?? [],
      })),
      proofs,
    },
  });
  return [
    make("Lax1", [{ conceptId: "Lax1.Base", imports: [] }]),
    make("Lax3", [{ conceptId: "Lax3.Middle", imports: ["Lax1.Base"] }]),
    make("Lax4", [
      { conceptId: "Lax4.Top", imports: ["Lax3.Middle"], statements: [{ id: "Lax4.Top.a", signature: "a : True" }] },
      { conceptId: "Lax4.Aux", imports: [], statements: [{ id: "Lax4.Aux.b", signature: "b : True" }] },
    ], [
      { id: "Lax4Proofs.a", path: "proofs/Lax4Proofs/A.lean", conclusion: "Lax4.Top.a", assumptions: ["Lax4.Aux.b"], description: "cycle a" },
      { id: "Lax4Proofs.b", path: "proofs/Lax4Proofs/B.lean", conclusion: "Lax4.Aux.b", assumptions: ["Lax4.Top.a"], description: "cycle b" },
    ]),
  ];
}

/** The submissions the landing page borrows from: the word RAM, the graph
 * encoding and the connected-components theorem with its proof (the third
 * example's cards), the network submission, and a foundation definition
 * another submission builds on. */
function landingArchive(): SiteSubmission[] {
  const make = (
    id: string,
    concepts: { conceptId: string; title: string; imports?: string[]; statements?: { id: string; signature: string }[] }[],
    proofs: NonNullable<SiteSubmission["output"]>["proofs"] = [],
  ): SiteSubmission => ({
    record: { specVersion: "1", id, state: "registered", createdAt: "2026-02-01T00:00:00Z" },
    output: {
      specVersion: "1", id,
      manifest: { specVersion: "1", id, leanVersion: "v4.30.0", mathlibVersion: "abc", title: `Title of ${id}`, authors: [], bibEntries: [] },
      abstract: "", requiredByConcepts: [], requiredByProofs: [],
      concepts: concepts.map(({ conceptId, title, imports, statements }) => ({
        id: conceptId, path: `concepts/${conceptId.replaceAll(".", "/")}.lean`, title,
        type: statements?.length ? "theorem" : "definition",
        description: `About ${title}.`, imports: imports ?? [], mathlibImports: [],
        sourceText: `namespace ${conceptId}\n${statements?.length ? `axiom ${statements[0]!.id.split(".").pop()} : True` : "def x : ℕ := 0"}\nend ${conceptId}\n`,
        statements: (statements ?? []).map((s) => ({ ...s, startLine: 2, endLine: 2 })),
      })),
      proofs,
    },
  });
  return [
    make("lax-67", [{ conceptId: "Lax67.Ram", title: "The word RAM" }]),
    make("lax-11", [
      { conceptId: "Lax11.GraphEncoding", title: "Compressed sparse row encoding of a graph", imports: ["Lax67.Ram"] },
      { conceptId: "Lax11.ConnectedComponents", title: "Connected components in linear time", imports: ["Lax11.GraphEncoding"], statements: [{ id: "Lax11.ConnectedComponents.exists_linearTime_program_ccLabels", signature: "exists_linearTime_program_ccLabels : True" }] },
    ], [
      { id: "Lax11Proofs.CCMain.exists_linearTime_program_ccLabels", path: "proofs/Lax11Proofs/CCMain.lean", conclusion: "Lax11.ConnectedComponents.exists_linearTime_program_ccLabels", assumptions: [], description: "Breadth-first search." },
    ]),
    make("lax-17", [
      { conceptId: "Lax17.Treewidth", title: "Treewidth" },
      { conceptId: "Lax17.PolynomialGridMinor", title: "The grid-minor theorem", imports: ["Lax17.Treewidth"], statements: [{ id: "Lax17.PolynomialGridMinor.polynomial_grid_minor", signature: "polynomial_grid_minor : True" }] },
    ], [
      { id: "Lax17Proofs.Final.polynomial_grid_minor", path: "proofs/Lax17Proofs/Final.lean", conclusion: "Lax17.PolynomialGridMinor.polynomial_grid_minor", assumptions: [], description: "The main proof." },
    ]),
    make("lax-48", [{ conceptId: "Lax48.TwinWidth", title: "Twin-width" }]),
    make("lax-49", [{ conceptId: "Lax49.FunctionalEquivalence", title: "Functional equivalence", imports: ["Lax48.TwinWidth"] }]),
  ];
}

function snapshot(root: string): Map<string, Buffer> {
  const out = new Map<string, Buffer>();
  const walk = (dir: string) => {
    for (const name of fs.readdirSync(dir).sort()) {
      const file = path.join(dir, name);
      if (fs.statSync(file).isDirectory()) walk(file);
      else out.set(path.relative(root, file), fs.readFileSync(file));
    }
  };
  walk(root);
  return out;
}

describe("site generator", () => {
  it("labels superseded submission states as outdated", () => {
    expect(statePill("superseded")).toBe('<span class="status-pill state-superseded">outdated</span>');
  });

  it("builds provider-aware immutable source links", () => {
    const commit = "a".repeat(40);
    const cases = [
      {
        repository: "https://github.com/example/math",
        provider: "GitHub",
        file: `https://github.com/example/math/blob/${commit}/submission/concepts/Lax2/C.lean#L12`,
      },
      {
        repository: "https://gitlab.com/group/subgroup/math",
        provider: "GitLab",
        file: `https://gitlab.com/group/subgroup/math/-/blob/${commit}/submission/concepts/Lax2/C.lean#L12`,
      },
      {
        repository: "https://codeberg.org/example/math",
        provider: "Codeberg",
        file: `https://codeberg.org/example/math/src/commit/${commit}/submission/concepts/Lax2/C.lean#L12`,
      },
      {
        repository: "https://bitbucket.org/example/math",
        provider: "Bitbucket",
        file: `https://bitbucket.org/example/math/src/${commit}/submission/concepts/Lax2/C.lean#C.lean-12`,
      },
    ];
    for (const entry of cases) {
      const href = repositorySource(
        entry.repository,
        commit,
        "submission",
        "concepts/Lax2/C.lean",
        12,
      );
      expect(href).toBe(entry.file);
      expect(sourceProviderName(href!)).toBe(entry.provider);
    }
    expect(repositorySource("https://example.com/example/math", commit, ".")).toBeUndefined();
    expect(repositorySource("https://constructor/example/math", commit, ".")).toBeUndefined();
    expect(repositorySource("http://github.com/example/math", commit, ".")).toBeUndefined();
    expect(repositorySource("https://token@github.com/example/math", commit, ".")).toBeUndefined();
  });

  it("renders GitLab source actions for nested-group repositories", async () => {
    const root = tmpDir("lax-site-gitlab-source-");
    const values = submissions();
    values[0]!.record.source!.repository = "https://gitlab.com/group/subgroup/math";
    await generateSite(values, root);
    const submission = fs.readFileSync(path.join(root, "Lax2", "index.html"), "utf8");
    const concept = fs.readFileSync(path.join(root, "Lax2", "Lax2.C.html"), "utf8");
    const proof = fs.readFileSync(path.join(root, "Lax2", "Lax2Proofs.truth.html"), "utf8");
    expect(submission).toContain("GitLab @aaaaaaa");
    expect(submission).toContain("proofs/ on GitLab");
    expect(submission).toContain(`gitlab.com/group/subgroup/math/-/tree/${"a".repeat(40)}/proofs`);
    expect(concept).toContain("view on GitLab");
    expect(concept).toContain(`gitlab.com/group/subgroup/math/-/blob/${"a".repeat(40)}/concepts/Lax2/C.lean`);
    expect(proof).toContain("Read the Lean proof on GitLab");
  });

  it("uses numeric archive ordering", () => {
    expect(["Lax10", "Lax2", "Lax1"].sort(compareIds)).toEqual(["Lax1", "Lax2", "Lax10"]);
    // The hyphenated spelling the database stores sorts numerically too —
    // read as text, `lax-10` would come before `lax-3`.
    expect(["lax-10", "lax-3", "lax-62", "lax-9"].sort(compareIds))
      .toEqual(["lax-3", "lax-9", "lax-10", "lax-62"]);
    // Mixed spellings still order by the number they share.
    expect(["Lax10", "lax-3"].sort(compareIds)).toEqual(["lax-3", "Lax10"]);
    // An id carrying no archive number sorts last, and by name among its kind.
    expect(["lax-3", "draft-b", "draft-a"].sort(compareIds))
      .toEqual(["lax-3", "draft-a", "draft-b"]);
  });

  it("lists the archive in numeric order for hyphenated database ids", async () => {
    const all = graphSubmissions();
    // The spelling the live database uses, at numbers where text order and
    // numeric order disagree.
    for (const [index, id] of ["lax-3", "lax-10", "lax-62"].entries()) {
      all[index]!.record.id = id;
      all[index]!.output!.id = id;
    }
    expect(new SiteModel(all).submissions.map((s) => s.record.id))
      .toEqual(["lax-3", "lax-10", "lax-62"]);

    const root = tmpDir("lax-site-idorder-");
    await generateSite(all, root);
    const html = fs.readFileSync(path.join(root, "index.html"), "utf8");
    const listed = [...html.matchAll(/class="submissions-list-link" href="(lax-\d+)\//g)]
      .map((match) => match[1]);
    expect(listed).toEqual(["lax-3", "lax-10", "lax-62"]);
  });

  it("derives complete topic phrases from submission and concept titles", async () => {
    const make = (id: string, title: string, conceptTitles: string[]): SiteSubmission => ({
      record: { specVersion: "1", id, state: "registered", createdAt: "2026-01-01T00:00:00Z" },
      output: {
        specVersion: "1", id,
        manifest: { specVersion: "1", id, leanVersion: "v4", mathlibVersion: "x", title, authors: [], bibEntries: [] },
        abstract: "", requiredByConcepts: [], requiredByProofs: [], proofs: [],
        concepts: conceptTitles.map((conceptTitle, index) => ({
          id: `${id}.C${index}`, path: "", title: conceptTitle, type: "definition",
          description: "", imports: [], sourceText: "", statements: [],
        })),
      },
    });
    const archive = [
      make("Lax1", "Linear Neighbourhood Complexity", ["Neighbourhood complexity"]),
      make("Lax2", "Almost Linear Neighborhood Complexity", ["Neighborhood complexity"]),
      make("Lax3", "Finite Ramsey Theorems", ["Ramsey's theorem for pairs"]),
    ];
    const index = submissionTagIndex(archive);
    const neighborhood = index.tags.find((tag) => tag.key === "neighborhood complexity");
    expect(neighborhood?.submissionIds).toEqual(["Lax1", "Lax2"]);
    expect(index.tags.some((tag) => tag.key === "ramsey theorem")).toBe(true);
    expect(index.tags.some((tag) => tag.key === "neighborhood")).toBe(false);
    expect(index.bySubmission.get("Lax3")).toContain("ramsey theorem");

    const root = tmpDir("lax-site-tags-");
    await generateSite(archive, root);
    const html = fs.readFileSync(path.join(root, "index.html"), "utf8");
    expect(html).toContain('<h4 id="tag-browser-heading">Browse by topic</h4>');
    expect(html).toContain("Suggested from submission and concept titles.");
    expect(html).toContain('data-tag-filter="" aria-pressed="true"');
    expect(html).toContain('id="tag-results-status" aria-live="polite"');
    expect(html).toContain('data-tags="|');
  });

  it("compresses concept types to 3-letter badges and rejects a missing type", () => {
    expect(typeBadgeText("theorem")).toBe("thm");
    expect(typeBadgeText("Definition")).toBe("def");
    expect(typeBadgeText("proposition")).toBe("prp");
    expect(typeBadgeText("conjecture")).toBe("con");
    expect(() => typeBadgeText(undefined)).toThrow("type is required");
  });

  it("uses count-free aggregate concept statuses", () => {
    expect(countsPill(0, 0)).toContain(">definition</span>");
    expect(countsPill(2, 2)).toContain(">proven</span>");
    expect(countsPill(1, 2)).toContain(">open</span>");
    expect(countsPill(1, 2)).not.toContain("1 of");
    expect(typeBadge("theorem", true)).toContain(">thm✓</span>");
    expect(typeBadge("theorem", false)).toContain(">thm×</span>");
    // a badge carrying a status mark joins the green/yellow status classes
    expect(typeBadge("theorem", true)).toContain('class="type-badge proven"');
    expect(typeBadge("theorem", false)).toContain('class="type-badge open"');
    expect(typeBadge("theorem")).toContain('class="type-badge"');
  });

  it("resolves crossrefs, renders math, and marks bad references", () => {
    const model = new SiteModel(submissions());
    const html = new MarkdownRenderer(model).render(submissions()[0]!.output!.abstract, "../");
    expect(html).toContain('../Lax2/Lax2.C.html');
    expect(html).toContain('#s-Lax2.C.truth');
    expect(html).toContain('class="katex"');
    expect(html).toContain('class="xref xref-broken"');
  });

  it("renders inline math spans across hard-wrapped lines without swallowing prose", () => {
    const markdown = new MarkdownRenderer(new SiteModel(submissions()));
    const html = markdown.render("for every $\\varepsilon >\n0$ there is a $c$ such that", "");
    // Both spans render; the prose between them stays prose.
    expect((html.match(/class="katex"/g) ?? []).length).toBe(2);
    expect(html).toContain("there is a");
    expect(html).toContain("such that");
  });

  it("renders dollar and backtick math in author prose while preserving ordinary inline code", () => {
    const markdown = new MarkdownRenderer(new SiteModel(submissions()));
    const html = markdown.renderAuthorProse("The values $x^2$ and `y_i` agree.", "");
    expect((html.match(/class="katex"/g) ?? []).length).toBe(2);
    expect(html).not.toContain("<code>y_i</code>");

    const ordinary = markdown.render("Run `lax build` to continue.", "");
    expect(ordinary).toContain("<code>lax build</code>");
    expect(ordinary).not.toContain('class="katex"');
  });

  it("renders standard TeX delimiters alongside Markdown in author prose", () => {
    const markdown = new MarkdownRenderer(new SiteModel(submissions()));
    const html = markdown.renderAuthorProse(String.raw`**Regular** when \(\varepsilon > 0\).

\[
  m_0 \le k \le M
\]

- one *equitable* partition`, "");
    expect((html.match(/class="katex"/g) ?? []).length).toBe(2);
    expect(html).toContain("<strong>Regular</strong>");
    expect(html).toContain("<em>equitable</em>");
    expect(html).toContain("<ul>");
    expect(html).not.toContain("\\(\\varepsilon");
    expect(html).not.toContain("\\[");
  });

  it("lets display math interrupt author prose without surrounding blank lines", () => {
    const markdown = new MarkdownRenderer(new SiteModel(submissions()));
    const html = markdown.renderAuthorProse(String.raw`Before the formula.
$$
  x^2 + y^2 = z^2
$$
After the formula.`, "");
    expect(html).toContain('<span class="katex-display">');
    expect(html).toContain("<p>Before the formula.</p>");
    expect(html).toContain("<p>After the formula.</p>");
    expect(html).not.toContain("$$");
  });

  it("renders display math in abstracts and theorem statement boxes", async () => {
    const authored = submissions();
    const output = authored[0]!.output!;
    output.abstract = "Moser--Tardos before abstract math.\n$$a^2$$\nAfter abstract math.";
    output.concepts[0]!.description = "Chuzhoy--Tan before theorem math.\n$$b^2$$\nAfter theorem math.";

    const root = tmpDir("lax-site-display-math-");
    await generateSite(authored, root);
    const submission = fs.readFileSync(path.join(root, "Lax2", "index.html"), "utf8");
    const concept = fs.readFileSync(path.join(root, "Lax2", "Lax2.C.html"), "utf8");
    expect(submission).toMatch(/paper-abstract[^]*?class="katex-display"/);
    expect(submission).toContain("Moser–Tardos before abstract math.");
    expect(submission).not.toContain("Moser--Tardos");
    expect(submission).toContain("<p>After abstract math.</p>");
    expect(concept).toMatch(/block block-statement[^]*?class="katex-display"/);
    expect(concept).toContain("Chuzhoy–Tan before theorem math.");
    expect(concept).not.toContain("Chuzhoy--Tan");
    expect(concept).toContain("<p>After theorem math.</p>");
  });

  it("applies TeX-style en dashes only to authored prose text", () => {
    const markdown = new MarkdownRenderer(new SiteModel(submissions()));
    const html = markdown.renderAuthorProse("Moser--Tardos and $a--b$.", "");
    expect(html).toContain("Moser–Tardos");
    expect(html).toContain(">a--b</annotation>");
  });

  it("renders safe inline Markdown and TeX without block wrappers for titles", () => {
    const markdown = new MarkdownRenderer(new SiteModel(submissions()));
    const html = markdown.renderAuthorInline(String.raw`A **sharp** \(x^2\) [bound](https://example.com) [[Lax2.C]] <img src=x>`, "");
    expect(html).toContain("A <strong>sharp</strong>");
    expect(html).toContain('class="katex"');
    expect(html).toContain("bound");
    expect(html).toContain("<code>Lax2.C</code>");
    expect(html).toContain("&lt;img src=x&gt;");
    expect(html).not.toContain("<p>");
    expect(html).not.toContain("<a href=");
    expect(html).not.toContain("<img src=x>");
  });

  it("renders authored submission, concept, and annotation titles", async () => {
    const authored = submissions();
    const output = authored[0]!.output!;
    output.manifest.title = String.raw`A **sharp** \(x^2\) bound`;
    output.concepts[0]!.title = String.raw`The *small* \(y_i\) lemma`;
    output.concepts[0]!.sections = [{ title: String.raw`Case \(z\)`, markdown: "Concept notes." }];
    output.proofs[0]!.sections = [{ title: String.raw`Step \(w\)`, markdown: "Proof notes." }];

    const root = tmpDir("lax-site-author-titles-");
    await generateSite(authored, root);
    const index = fs.readFileSync(path.join(root, "index.html"), "utf8");
    const submission = fs.readFileSync(path.join(root, "Lax2", "index.html"), "utf8");
    const concept = fs.readFileSync(path.join(root, "Lax2", "Lax2.C.html"), "utf8");
    const proof = fs.readFileSync(path.join(root, "Lax2", "Lax2Proofs.truth.html"), "utf8");

    for (const html of [index, submission]) {
      expect(html).toContain("<strong>sharp</strong>");
      expect(html).toContain('class="katex"');
    }
    expect(submission.match(/<title>(.*?)<\/title>/s)?.[1]).toContain("**sharp**");
    expect(concept).toContain("<title>The small y_i lemma</title>");
    expect(concept).toContain('<span class="entry-label-text">The small y_i lemma</span>');
    expect(concept).toMatch(/<h1 class="concept-title">The <em>small<\/em> <span class="katex"/);
    expect(concept).toMatch(/<h3>Case <span class="katex"/);
    expect(proof).toMatch(/<h3>Step <span class="katex"/);
    const graphMatch = /<script type="application\/json" id="graph-data">(.*?)<\/script>/s.exec(concept)!;
    expect(JSON.parse(graphMatch[1]!).concepts.nodes[0].title).toBe("The small y_i lemma");
  });

  it("uses all inline-math delimiters in abstracts and annotation comments", async () => {
    const authored = submissions();
    const output = authored[0]!.output!;
    const prose = "Dollar $x^2$, shorthand `y_i`, and TeX \\(z^3\\).";
    output.abstract = prose;
    output.concepts[0]!.description = prose;
    output.concepts[0]!.sections = [{ title: "Review notes", markdown: prose }];
    output.proofs[0]!.description = prose;
    output.proofs[0]!.sections = [{ title: "Strategy", markdown: prose }];

    const root = tmpDir("lax-site-author-math-");
    await generateSite(authored, root);
    for (const file of [
      path.join(root, "Lax2", "index.html"),
      path.join(root, "Lax2", "Lax2.C.html"),
      path.join(root, "Lax2", "Lax2Proofs.truth.html"),
    ]) {
      const html = fs.readFileSync(file, "utf8");
      expect((html.match(/class="katex"/g) ?? []).length).toBeGreaterThanOrEqual(3);
      expect(html).not.toContain("<code>y_i</code>");
    }
  });

  it("renders proof-network tooltip math at build time while keeping author HTML inert", async () => {
    const authored = submissions();
    const output = authored[0]!.output!;
    output.concepts[0]!.title = String.raw`A **sharp** $x^2$ bound with $$x \le y$$.`;
    output.proofs[0]!.description = String.raw`Use $y_i$ and $$\sum_{i=1}^n i = \frac{n(n+1)}{2}$$.
\[\frac{a}{b}\]
</script><img src=x onerror="alert(1)"> [link](javascript:alert(1)) $\badcommand$`;

    const root = tmpDir("lax-site-tooltip-math-");
    await generateSite(authored, root);
    const html = fs.readFileSync(path.join(root, "Lax2", "index.html"), "utf8");
    const graph = JSON.parse(/<script type="application\/json" id="graph-data">(.*?)<\/script>/s.exec(html)![1]!);
    const title = graph.proofs.statements[0].tooltipHtml;
    const description = graph.proofs.proofs[0].tooltipHtml;
    expect(title).toContain("<strong>sharp</strong>");
    expect(title.match(/class="katex"/g)).toHaveLength(2);
    expect(title.match(/class="katex-display"/g)).toHaveLength(1);
    expect(description.match(/class="katex"/g)).toHaveLength(3);
    expect(description.match(/class="katex-display"/g)).toHaveLength(2);
    expect(description).toContain('class="math-error"');
    expect(description).toContain("&lt;/script&gt;&lt;img");
    expect(description).not.toMatch(/<script|<img|<a\b/);
    expect(html).not.toContain('</script><img src=x');
    expect(graph.proofs.statements[0].title).toBe(output.concepts[0]!.title);
    expect(graph.proofs.proofs[0].description).toBe(output.proofs[0]!.description);
  });

  it("escapes crossref labels, preserves escaped syntax, and survives invalid TeX", () => {
    const markdown = new MarkdownRenderer(new SiteModel(submissions()));
    const html = markdown.render(String.raw`[[Lax2.C|<img src=x>]] \[[Lax2.C]] $\badcommand$`, "");
    expect(html).toContain("&lt;img src=x&gt;");
    expect(html).not.toContain("<img src=x>");
    expect(html).toContain("[[Lax2.C]]");
    expect(html).toContain('class="math-error"');
  });

  it("emits complete deterministic static output with known MIME types", async () => {
    expect(siteAssetPath("layout.js")).toContain(path.join("assets", "site", "layout.js"));
    expect(() => siteAssetPath("../package.json")).toThrow("escapes");
    const one = tmpDir("lax-site-one-");
    const two = tmpDir("lax-site-two-");
    await generateSite(submissions(), one);
    await generateSite(submissions(), two);
    const first = snapshot(one); const second = snapshot(two);
    expect([...first.keys()]).toEqual([...second.keys()]);
    for (const [name, bytes] of first) {
      expect(bytes.equals(second.get(name)!)).toBe(true);
      expect(SITE_MIME[path.extname(name)], `missing MIME for ${name}`).toBeDefined();
    }
    for (const asset of ["style.css", "sidebar.js", "landing.js", "layout.js", "dag.js", "source-proof.js", "citation.js", "version-history.js", "comments.js", "katex.css", "lax-white-paper.pdf", path.join("fonts", "LM-regular.woff2")])
      expect(fs.existsSync(path.join(one, "assets", asset)), asset).toBe(true);
    const emptySubmission = fs.readFileSync(path.join(one, "Lax10", "index.html"), "utf8");
    expect(emptySubmission).toContain('data-remark42-url="https://laxarchive.org/Lax10/"');
    expect(emptySubmission).toMatch(/<script src="\.\.\/assets\/comments\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(fs.readFileSync(path.join(one, "assets", "lax-white-paper.pdf")).subarray(0, 4).toString()).toBe("%PDF");
    // Graph containers must be measurable before dag.js appends their SVG.
    const css = fs.readFileSync(path.join(one, "assets", "style.css"), "utf8");
    expect(css).not.toContain(".figure-container:empty");
    expect(css).toContain(".graph-figure.graph-expanded");
    expect(css).toContain(".proof-network-figure > .graph-expand{ right: 1rem; }");
    expect(css).toContain(".graph-edge-casing{");
    expect(css).toContain("fill: context-stroke");
    expect(css).toContain("background: rgba(248, 250, 252, 0.98)");
    expect(css).toContain('.status-pill[data-tooltip]:hover::after');
    expect(css).not.toContain(".landing-demo-");
    expect(css).not.toContain(".landing-action-card");
    expect(css).not.toContain(".landing-review-start");
    expect(css).toContain("#detail .landing-title{");
    expect(css).toContain(".landing-passage.manuscript-hl-hover,");
    expect(css).not.toContain(".landing-passage::after");
    expect(css).toContain(".landing-paper-grid{\n  position: relative;");
    expect(css).toContain(".landing-carousel-slide{ min-width: 0; }");
    expect(css).toContain(".landing-carousel-slide-off{ position: absolute; top: 0; left: 0; right: 0; visibility: hidden; pointer-events: none; }");
    expect(css).toContain(".landing-carousel-arrow{");
    expect(css).toContain(".landing-network-viewport::before,");
    expect(css).toContain(".landing-plain-section{");
    expect(css).toContain(".landing-foundation{");
    expect(css).not.toContain("landing-carousel-count");
    expect(css).not.toContain(".landing-tile");
    expect(css).toContain(".submissions-list-clipped::after{");
    expect(css).toContain(".landing-paper-rail-live > .manuscript-card{ position: absolute; left: 0; right: 0; margin: 0; z-index: 6; }");
    expect(css).toContain(".landing-paper-rail-live > .manuscript-card{ position: static; margin: 0 0 0.5rem; }");
    expect(css).toContain(".landing-paper-grid{ grid-template-columns: 1fr; row-gap: 0.9rem; }");
    expect(css).toContain(".entry-label .concept-review-badge.pending{ display: none; }");
    expect(css).toContain("@keyframes concept-review-loading");
    expect(css).toContain(".submissions-load-more[hidden]{ display: none; }");
    expect(css).toContain(".landing-faq-item summary::-webkit-details-marker{ display: none; }");
    expect(css).toContain(".landing-faq-item[open] .landing-faq-toggle::after");
    const faqPanel = css.match(/\n\.landing-faq\{([^}]*)\}/)?.[1] ?? "";
    expect(faqPanel).toContain("border: 1px solid var(--border)");
    expect(faqPanel).toContain("margin: 0");
    const faqList = css.match(/\.landing-faq-list\{([^}]*)\}/)?.[1] ?? "";
    expect(faqList).toContain("border: 0");
    expect(faqList).toContain("border-top: 1px solid var(--border-light)");
    const landingScript = fs.readFileSync(path.join(one, "assets", "landing.js"), "utf8");
    const sidebarScript = fs.readFileSync(path.join(one, "assets", "sidebar.js"), "utf8");
    expect(landingScript).toContain("target.scrollIntoView({ behavior, block: 'start' })");
    expect(landingScript).toContain("url.searchParams.set('view', id)");
    expect(landingScript).toContain("window.addEventListener('popstate'");
    expect(landingScript).toContain("const initialView = urlView()");
    expect(landingScript).toContain("document.getElementById(`landing-panel-${id}`)");
    expect(landingScript).toContain("function setupCardBox(box)");
    expect(landingScript).toContain("document.querySelectorAll('[data-card-box]')");
    expect(landingScript).toContain("box.querySelectorAll('.manuscript-card')");
    expect(landingScript).toContain("rail.classList.add('landing-paper-rail-live')");
    expect(landingScript).toContain("function drawLinks()");
    expect(landingScript).toContain("links.classList.add('manuscript-links-live')");
    expect(landingScript).toContain("pair.link.setAttribute('class', `manuscript-link kind-${pair.passage.dataset.kind || 'concept'}`)");
    expect(landingScript).toContain("new ResizeObserver(() => layout())");
    expect(landingScript).toContain("card.classList.toggle('manuscript-card-pinned', next)");
    expect(landingScript).toContain("passage.setAttribute('aria-pressed', String(next))");
    // A card open under the pointer takes no room; on a phone the cards go under their passages.
    expect(landingScript).toContain("pair.opening || pair.pinned ? card.offsetHeight : closedHeight(card)");
    expect(landingScript).toContain("card.classList.add('landing-card-inline')");
    expect(landingScript).toContain("if (passage.nextElementSibling !== card) passage.after(card)");
    expect(landingScript).toContain("window.matchMedia('(hover: hover)')");
    expect(landingScript).toContain("window.matchMedia('(max-width: 640px)')");
    expect(landingScript).toContain("function setupCarousel(root)");
    expect(landingScript).toContain("document.querySelectorAll('[data-carousel]')");
    expect(landingScript).toContain("slide.classList.toggle('landing-carousel-slide-off', !selected)");
    expect(landingScript).toContain("function setupNetwork()");
    expect(landingScript).toContain("container.scrollLeft = Math.max(0, (container.scrollWidth - container.clientWidth) / 2)");
    expect(landingScript).not.toContain("setupProofFlip");
    expect(landingScript).not.toContain("setupReviewConcept");
    expect(landingScript).not.toContain("data-copy-prompt");
    expect(landingScript).not.toContain("sessionStorage");
    const citationScript = fs.readFileSync(path.join(one, "assets", "citation.js"), "utf8");
    expect(citationScript).toContain("function setupCitationTour()");
    expect(citationScript).toContain('url.searchParams.get("tour") !== "citation"');
    expect(citationScript).toContain('target.scrollIntoView({ behavior, block: "start" })');
    expect(sidebarScript).toContain("document.querySelectorAll('[data-tag-filter]')");
    expect(sidebarScript).toContain("url.searchParams.set('tag', tag)");
    expect(sidebarScript).toContain("updateTagStatus(total, shown)");
    expect(sidebarScript).toContain("function applySidebarFilters()");
    expect(sidebarScript).toContain("el.dataset.searchTitle !== undefined");
    expect(sidebarScript).toContain("function applySubmissionFilters()");
    expect(sidebarScript).toContain("filterList(list, search, type, 'entry-list-empty');");
    expect(sidebarScript).not.toContain("filterList(list, search, type, 'entry-list-empty', selectedTag)");
    expect(sidebarScript).toContain("function setupRandomSubmission()");
    expect(sidebarScript).toContain("Math.floor(Math.random() * candidates.length)");
    expect(sidebarScript).toContain("randomSubmission.hidden = Boolean(searchEl?.value.length)");
    expect(sidebarScript).toContain("const SUBMISSION_PREVIEW_SIZE = 3");
    expect(sidebarScript).toContain("function applySubmissionPagination(list, total)");
    expect(sidebarScript).toContain("submissionVisibleLimit = Infinity");
    expect(sidebarScript).toContain("list.classList.toggle('submissions-list-clipped', clipped)");
    expect(sidebarScript).toContain("function setupSidebarResize()");
  });

  it("rejects generated page paths that escape the output directory", async () => {
    const root = tmpDir("lax-site-contained-");
    const outDir = path.join(root, "site");
    const outside = path.join(root, "index.html");
    fs.writeFileSync(outside, "preserved");
    const malicious = submissions();
    malicious[0]!.output!.concepts[0]!.id = "Lax42Proofs.x/../../../index";

    await expect(generateSite(malicious, outDir)).rejects.toThrow(
      "generated page escapes the site output directory",
    );
    expect(fs.readFileSync(outside, "utf8")).toBe("preserved");
    expect(fs.existsSync(outDir)).toBe(false);
  });

  it("renders the index with library rows and a searchable sidebar", async () => {
    const root = tmpDir("lax-site-index-");
    await generateSite(submissions(), root);
    const index = fs.readFileSync(path.join(root, "index.html"), "utf8");
    // Editorial text comes from content/ and the contributing page is live.
    expect(index).toContain("<title>Lax Lean Archive</title>");
    expect(index).toContain('Lax <span class="site-title-quiet">Lean Archive</span>');
    // The fixed site header supplies the title; the landing does not repeat it.
    expect(index).not.toContain('<h1 class="paper-title">Lax <span class="site-title-quiet">Lean Archive</span></h1>');
    expect(index).toContain(`<h1 class="landing-title" id="landing-title">Let's stay in control of mathematics</h1>`);
    expect(index).toContain('<div class="landing-manifesto latex-content">');
    expect(index).toMatch(/AI is about to massively accelerate mathematical research/);
    expect(index).not.toContain("<strong>Correctness</strong>");
    expect(index).not.toContain("<strong>Understanding</strong>");
    expect(index).toContain('<section class="landing-section landing-how" aria-labelledby="landing-how-heading">');
    expect(index).toContain('<h2 class="landing-section-title" id="landing-how-heading">How it works</h2>');
    expect(index).not.toContain("landing-paper-caption");
    expect(index.indexOf("landing-hero")).toBeLessThan(index.indexOf("landing-how"));
    expect(index.indexOf("landing-how")).toBeLessThan(index.indexOf("landing-plain-section"));
    expect(index).not.toContain("landing-hero-actions");
    expect(index.indexOf("landing-plain-section")).toBeLessThan(index.indexOf('id="landing-library-heading"'));
    // Getting started: a plain section with the two commands, no tiles.
    expect(index).toContain('<h2 class="landing-section-title" id="landing-start-heading">Get started right away</h2>');
    expect(index).toContain("npm install -g lax-archive &amp;&amp; lax doctor");
    expect(index).toContain("Run `lax print instructions` and follow the guide it prints");
    expect(index).not.toContain("landing-tile");
    expect(index).not.toContain("landing-column");
    expect(index).not.toContain("What it is for");
    expect(index).not.toContain("Browse submissions");
    expect(index).not.toContain("landing-links-note");
    // The examples written for the page are always there; the one drawn
    // from the archive (the word RAM) needs its concepts, and the network
    // needs its submission. Neither is in the fixture archive, nor the
    // introduction, so the paper link falls back to the white paper and no
    // foundation is listed.
    expect(index).toContain('data-carousel>');
    expect(index).toContain('id="landing-example-primes"');
    expect(index).toContain('id="landing-example-ramsey"');
    expect(index).not.toContain('id="landing-example-ram"');
    expect(index).toContain('aria-label="Excerpts of 2 annotated papers, as the archive shows them: a paper on prime numbers, a paper on Ramsey\'s theorem"');
    expect(index).not.toContain('id="proof-network"');
    expect(index).not.toContain('id="graph-data"');
    expect(index).not.toContain("landing-foundations");
    expect(index).toContain('<div class="landing-paper-foot"><a class="landing-paper-more" href="assets/lax-white-paper.pdf" download="lax-white-paper.pdf">Read the Lax paper</a></div>');
    expect(index).not.toContain("See full submission");
    expect(index).not.toContain("landing-cta");
    expect(index).not.toMatch(/<script src="assets\/dag\.js/);
    // The old landing's parts are gone.
    expect(index).not.toContain("What you can do here");
    expect(index).not.toContain("landing-demo-card");
    expect(index).not.toContain("landing-action-card");
    expect(index).not.toContain('id="landing-panel-submit"');
    expect(index).not.toContain('id="landing-panel-review"');
    expect(index).not.toContain('id="landing-proof-obligations"');
    expect(index).not.toContain("data-review-concept");
    expect(index).toContain('<section class="landing-action-panel submissions-library" id="landing-panel-read" aria-labelledby="landing-library-heading">');
    expect(index).toContain('<h2 class="landing-section-title" id="landing-library-heading">Submissions</h2>');
    expect(index).not.toContain("Read the archive");
    expect(index).toContain('<section class="landing-faq" id="faq" aria-labelledby="landing-faq-heading">');
    expect(index).toContain('<h2 class="landing-section-title landing-faq-title" id="landing-faq-heading">FAQ</h2>');
    expect(index).toContain('<ol class="landing-faq-list">');
    expect(index).toContain('<li class="landing-faq-list-item"><details class="landing-faq-item">');
    expect(index.match(/<details class="landing-faq-item">/g)).toHaveLength(8);
    expect(index).toContain("How do I create my own submission?");
    expect(index).toContain("How does Lax relate to projects such as Merely True and Tau Ceti?");
    expect(index).toContain("Can I use Lax for anonymous peer review?");
    expect(index).toContain("Which operating systems does Lax support?");
    expect(index).toContain('href="https://palomar-registry.org/"');
    expect(index.indexOf('id="landing-panel-read"')).toBeLessThan(index.indexOf('id="faq"'));
    expect(index).not.toMatch(/id="landing-panel-read"[^>]* hidden/);
    expect(index).toContain("contributing.html");
    expect(index).toMatch(/<script src="assets\/landing\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(index).toMatch(/<script src="assets\/sidebar\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(index).toMatch(/<script src="assets\/account\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(index).toContain('data-account-login');
    expect(index).toContain('data-account-settings');
    expect(index).toContain('<nav class="header-actions" aria-label="Account">');
    expect(index).toContain('id="sidebar-resizer" class="sidebar-resizer" role="separator" aria-label="Resize sidebar"');
    expect(index).not.toContain('class="header-submit"');
    expect(index).toContain('<span>Sign in<span class="account-login-long"> with ORCID</span></span>');
    expect(index).toContain('id="account-dialog"');
    expect(index).not.toContain('href="all-comments/');
    expect(index).toMatch(/<link rel="stylesheet" href="assets\/style\.css\?v=[0-9a-f]{12}">/);
    expect(index).not.toContain("&lt;!--");
    expect(index).toContain("Lax2/index.html");
    expect(index).toContain('class="submissions-list-link');
    expect(index).toContain('<span class="submissions-list-title">Two<span class="submissions-list-date">(2026-01-02)</span>');
    const submissionsList = index.slice(index.indexOf('<ul class="submissions-list"'), index.indexOf("</ul>", index.indexOf('<ul class="submissions-list"')));
    expect(submissionsList).not.toContain('class="submission-title-id"');
    expect(submissionsList).not.toContain('class="submission-title-inline-separator"');
    expect(index).not.toContain('<span class="submissions-list-counts"><code>Lax2</code>');
    expect(index).toContain("2 concepts, 1 proof");
    expect(index).toContain('<span class="formalized-label">formalized by</span> Alice');
    expect(index).toContain('id="filter-search"');
    expect(index).toContain('data-search-title="lax2 two"');
    expect(index).toContain('data-search-concepts="lax2.c truth theorem lax2.d definition helper definition"');
    expect(index).toContain('data-state="registered"');
    expect(index).toContain('placeholder="Search titles and concepts"');
    expect(index).toContain('<section class="random-submission" aria-labelledby="random-submission-heading">');
    expect(index).toContain('<h2 id="random-submission-heading">Explore a random submission</h2>');
    expect(index).toContain('href="Lax2/index.html" data-random-submission-link');
    expect(index).toContain('href="Lax2/index.html" data-random-submission-candidate');
    const randomSubmission = index.slice(index.indexOf('<section class="random-submission"'), index.indexOf("</section>"));
    expect(randomSubmission).toContain('<span class="random-submission-title">Two</span>');
    expect(randomSubmission).not.toContain('class="entry-id"');
    expect(index.indexOf('class="random-submission"')).toBeGreaterThan(index.indexOf('class="sidebar-filters"'));
    expect(index.indexOf('class="random-submission"')).toBeLessThan(index.indexOf('<ul id="entry-list">'));
    expect(index).toContain('id="submissions-list"');
    expect(index).toContain('id="submissions-list-empty"');
    expect(index).toContain('<button class="submissions-load-more" id="submissions-load-more" type="button" aria-controls="submissions-list" hidden>Show all 1 submission <b aria-hidden="true">↓</b></button>');
    // sidebar rows share the flat entry grammar and use titles alone
    expect(index).not.toContain("sidebar-submission");
    expect(index).toContain('data-entry-group="registered">Registered</li>');
    expect(index).toContain('<span class="entry-label"><span class="entry-label-text">Two</span></span>');
    expect(index).not.toContain('<span class="entry-id">');
    expect(index).toContain('href="Lax2/index.html" data-full-title="Two"');
    // a record that only reserved an id stays off the landing page, the
    // sidebar, and the stats; its page still exists for direct links
    expect(index).not.toContain("Lax10");
    expect(index).not.toContain("no content uploaded yet");
    expect(index).toContain("1 submission ·");
    const contributing = fs.readFileSync(path.join(root, "contributing.html"), "utf8");
    expect(contributing).toContain('<h1 class="paper-title">Getting started</h1>');
    expect(contributing).toContain("The workflow");
    expect(contributing).not.toContain('class="random-submission"');
    const proofObligations = fs.readFileSync(path.join(root, "open-proof-obligations.html"), "utf8");
    expect(proofObligations).toContain("<title>Open Proof Obligations — Lax Lean Archive</title>");
    expect(proofObligations).toContain("There are currently no open proof obligations");
    expect(fs.readFileSync(path.join(root, "open-problems.html"), "utf8")).toBe(proofObligations);
  });

  it("shows the examples, the network and the foundations from the archive", async () => {
    const root = tmpDir("lax-site-intro-");
    await generateSite([...submissions(), introSubmission(), ...landingArchive()], root);
    const index = fs.readFileSync(path.join(root, "index.html"), "utf8");

    // The examples box: a dot per example, an arrow either side, three
    // slides, the first selected, the others invisible and inert.
    expect(index).toContain('<section class="landing-box landing-paper manuscript" aria-label="Excerpts of 3 annotated papers, as the archive shows them: a paper on prime numbers, a paper on Ramsey\'s theorem, a paper on algorithms on a random access machine" data-carousel>');
    expect(index).toContain('<div class="landing-box-head">');
    expect(index).toContain('<div class="landing-carousel-dots" role="tablist" aria-label="Examples">');
    expect(index).toContain('<button class="landing-carousel-dot" role="tab" type="button" id="landing-tab-primes" aria-selected="true" aria-controls="landing-example-primes" aria-label="Example 1 of 3: a paper on prime numbers" tabindex="0"></button>');
    expect(index).toContain('<button class="landing-carousel-dot" role="tab" type="button" id="landing-tab-ramsey" aria-selected="false" aria-controls="landing-example-ramsey" aria-label="Example 2 of 3: a paper on Ramsey\'s theorem" tabindex="-1"></button>');
    expect(index).toContain('<button class="landing-carousel-dot" role="tab" type="button" id="landing-tab-ram" aria-selected="false" aria-controls="landing-example-ram" aria-label="Example 3 of 3: a paper on algorithms on a random access machine" tabindex="-1"></button>');
    expect(index).toContain('<button class="landing-carousel-arrow landing-carousel-arrow-prev" type="button" data-carousel-step="-1" aria-label="Previous example" title="Previous example (←)">');
    expect(index).toContain('<button class="landing-carousel-arrow landing-carousel-arrow-next" type="button" data-carousel-step="1" aria-label="Next example" title="Next example (→)">');
    expect(index).toContain('<div class="landing-carousel-slide" role="tabpanel" id="landing-example-primes" aria-labelledby="landing-tab-primes" data-card-box data-paper-excerpt>');
    expect(index).toContain('<div class="landing-carousel-slide landing-carousel-slide-off" role="tabpanel" id="landing-example-ramsey" aria-labelledby="landing-tab-ramsey" aria-hidden="true" inert data-card-box data-paper-excerpt>');
    // The primes example: definition, lemma, its proof, theorem, its proof
    // (which rests on the lemma); the first card open, not pinned.
    expect(index).toContain("Lorem ipsum dolor sit amet");
    expect(index).toContain('<div class="landing-passage landing-passage-1 kind-concept" role="button" tabindex="0" aria-pressed="false" aria-controls="landing-primes-1" aria-label="Definition 1, prime numbers: show the concept card" data-excerpt-card="landing-primes-1" data-kind="concept">');
    expect(index).toContain("<strong>Definition 1.</strong> A natural number greater than 1 is <em>prime</em>");
    expect(index).toContain('<div class="landing-passage landing-passage-3 kind-proof" role="button" tabindex="0" aria-pressed="false" aria-controls="landing-primes-3" aria-label="Proof of Lemma A: show the proof card" data-excerpt-card="landing-primes-3" data-kind="proof">');
    expect(index).toContain('aria-label="Theorem B, Euclid\'s theorem: show the concept card"');
    // Every card closed, a hint under them.
    expect(index).toContain('<li class="manuscript-card kind-concept line-proven" id="landing-primes-1">');
    expect(index).toContain('<li class="manuscript-card kind-concept line-proven" id="landing-primes-2">');
    expect(index).toContain('<li class="manuscript-card kind-proof line-proven" id="landing-primes-5">');
    expect(index).not.toContain("manuscript-card-expanded");
    expect(index).toContain('<div class="manuscript-card-body" id="landing-primes-1-body" hidden>');
    expect(index).toContain('<li class="landing-paper-hint" aria-hidden="true"><span class="landing-paper-hint-hover">Hover a highlight to expand</span>');
    expect(index).not.toContain("manuscript-card-pinned");
    expect(index).toContain('<span class="manuscript-card-name"><span class="type-badge" title="definition">def</span><code>Primes</code></span>');
    expect(index).toContain('<p class="manuscript-card-title">Prime numbers</p>');
    // One claim per concept, named in the head: no claims list, no page.
    expect(index).not.toContain('<ul class="manuscript-card-claims">');
    expect(index).not.toContain("manuscript-card-page");
    // The proof of Theorem B rests on the lemma; the proof of the lemma on nothing.
    const euclid = index.slice(index.indexOf('id="landing-primes-5-body"'), index.indexOf('id="landing-example-ramsey"'));
    expect(euclid).toContain('<div class="judgment-assumptions"><ul><li>');
    expect(euclid).toContain("<code>PrimeDivisor</code>");
    expect(euclid).toContain("<code>Euclid</code>");
    const primeDivisor = index.slice(index.indexOf('id="landing-primes-3-body"'), index.indexOf("</li>", index.indexOf('id="landing-primes-3-body"')));
    expect(primeDivisor).toContain('<p class="judgment-unconditional">no assumptions</p>');
    // Written cards link nowhere; the slide leads into the introduction.
    expect(index).not.toContain('<a href="lax-242665/Lax242665.Primes.html">');
    expect(index).toContain('<div class="landing-paper-foot"><a class="landing-paper-more" href="lax-242665/paper.html">Read full introduction to Lax</a></div>');
    // The word RAM example draws the archive\'s own cards, linked from the site root.
    expect(index).toContain('aria-controls="landing-ram-1" aria-label="Definition 1, the word RAM: show the concept card"');
    expect(index).toContain('<li class="manuscript-card kind-concept" id="landing-ram-1" data-mark="1">');
    expect(index).toContain('<a href="lax-67/Lax67.Ram.html"><code>Lax67.Ram</code></a>');
    expect(index).toContain('<a href="lax-11/Lax11.ConnectedComponents.html"><code>Lax11.ConnectedComponents</code></a>');
    expect(index).toContain('<li class="manuscript-card kind-proof line-proven" id="landing-ram-4" data-mark="4">');
    expect(index).toContain('<a href="lax-11/Lax11Proofs.CCMain.exists_linearTime_program_ccLabels.html"><code>Lax11Proofs.CCMain.exists_linearTime_program_ccLabels</code></a>');
    expect(index).toContain('<div class="landing-paper-foot"><a class="landing-paper-more" href="lax-11/index.html">See full submission</a></div>');
    expect(index).not.toContain('href="../lax-11/');
    expect(index).toContain('<ol class="manuscript-rail landing-paper-rail" aria-label="Cards">');
    expect(index).toContain('<svg class="manuscript-links landing-paper-links" aria-hidden="true"></svg>');
    // Captions sit inside the boxes.
    expect(index).toContain('<div class="landing-box-caption latex-content">');
    expect(index).toContain("<strong>The paper stays the paper.</strong>");
    expect(index).toContain("<strong>Proof network.</strong> Explore how proofs compose");
    expect(index).not.toContain("<strong>Proofs compose.</strong>");
    // The network: the network submission\'s figure and data, rooted at the site.
    expect(index).toContain('<figure class="landing-box graph-figure proof-network-figure landing-network-figure" aria-label="The proof network of lax-17">');
    expect(index).not.toContain("landing-network-source");
    expect(index).toContain('<a href="open-proof-obligations.html">open obligation</a>, and every result');
    expect(index).toContain('<div class="landing-network-viewport">\n<div id="proof-network" class="figure-container" data-graph="proofs"></div>\n</div>');
    const data = JSON.parse(index.match(/<script type="application\/json" id="graph-data">(.*?)<\/script>/)![1]!);
    expect(Object.keys(data)).toEqual(["proofs"]);
    expect(data.proofs.home).toBe("lax-17");
    expect(data.proofs.statements.map((s: { id: string; href: string; proven: boolean }) => [s.id, s.href, s.proven])).toEqual([
      ["Lax17.PolynomialGridMinor.polynomial_grid_minor", "lax-17/Lax17.PolynomialGridMinor.html#s-Lax17.PolynomialGridMinor.polynomial_grid_minor", true],
    ]);
    expect(data.proofs.proofs[0].href).toBe("lax-17/Lax17Proofs.Final.polynomial_grid_minor.html");
    expect(index).toMatch(/<script src="assets\/layout\.js\?v=[0-9a-f]{12}"><\/script>\n<script src="assets\/dag\.js\?v=[0-9a-f]{12}"><\/script>\n<script src="assets\/landing\.js\?v=[0-9a-f]{12}"><\/script>/);
    // The one way in: the annotated paper.
    expect(index).toContain('<a class="site-nav-link" href="lax-242665/paper.html">Introduction</a>');
    expect(index).toContain('<a class="site-nav-link" href="about.html">About</a>');
    expect(index).not.toContain("landing-cta");
    expect(index).not.toContain("lax-white-paper.pdf\" download");
    // The foundations: the listed definitions the archive holds, with how
    // many further submissions build on them.
    expect(index).toContain('<h2 class="landing-section-title" id="landing-foundations-heading">Build foundations together</h2>');
    expect(index).toContain('<li><a class="landing-foundation" href="lax-67/Lax67.Ram.html" title="Lax67.Ram">\n<span class="type-badge" title="definition">def</span><span class="landing-foundation-title">The word RAM</span>\n<span class="landing-foundation-meta"><span class="submission-meta-id">lax-67</span><span class="landing-foundation-uses">built on in 1 further submission</span></span>\n</a></li>');
    expect(index).toContain('href="lax-48/Lax48.TwinWidth.html" title="Lax48.TwinWidth"');
    expect(index).toContain('<span class="submission-meta-id">lax-48</span><span class="landing-foundation-uses">built on in 1 further submission</span>');
    expect(index).not.toContain("Lax48.Treewidth");
    expect(index).not.toContain("Lax12.NowhereDenseClasses");
    // Examples, network, in that order, before the button; getting started
    // and the foundations after it.
    expect(index.indexOf('id="landing-how-heading"')).toBeLessThan(index.indexOf("data-carousel"));
    expect(index.indexOf("data-carousel")).toBeLessThan(index.indexOf('id="proof-network"'));
    expect(index.indexOf('id="proof-network"')).toBeLessThan(index.indexOf("landing-plain-section"));
    expect(index.indexOf("landing-plain-section")).toBeLessThan(index.indexOf("landing-foundations"));
    // The submission's own pages keep their `../` links.
    const submission = fs.readFileSync(path.join(root, "lax-242665", "index.html"), "utf8");
    expect(submission).toContain('"href":"../lax-242665/Lax242665Proofs.InfinitelyManyPrimes.exists_prime_gt.html"');
  });

  it("generates a direct-only all-comments activity page", async () => {
    const root = tmpDir("lax-site-all-comments-");
    await generateSite(submissions(), root);
    const activity = fs.readFileSync(path.join(root, "all-comments", "index.html"), "utf8");
    const index = fs.readFileSync(path.join(root, "index.html"), "utf8");

    expect(activity).toContain("<title>All comments — Lax Lean Archive</title>");
    expect(activity).toContain('id="all-comments"');
    expect(activity).toContain('data-identity-url="https://comments.laxarchive.org/reactions/v1/identity"');
    expect(activity).toMatch(/<script src="\.\.\/assets\/all-comments\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(activity).toContain("connect-src https://comments.laxarchive.org");
    expect(index).not.toContain('href="all-comments/');
  });

  it("offers every submission as a random sidebar choice only on the front page", async () => {
    const root = tmpDir("lax-site-random-submission-");
    await generateSite([...submissions(), ...graphSubmissions()], root);
    const index = fs.readFileSync(path.join(root, "index.html"), "utf8");
    const sidebar = index.slice(index.indexOf('<aside id="sidebar">'), index.indexOf("</aside>"));
    expect(sidebar.match(/data-random-submission-candidate/g)).toHaveLength(4);
    expect(sidebar).toContain('href="Lax4/index.html" data-random-submission-candidate');
    expect(sidebar).toContain("View submission");
    for (const pageName of [
      "contributing.html",
      path.join("Lax2", "index.html"),
      path.join("Lax2", "Lax2.C.html"),
      path.join("Lax2", "Lax2Proofs.truth.html"),
    ]) {
      const html = fs.readFileSync(path.join(root, pageName), "utf8");
      expect(html).not.toContain('class="random-submission"');
    }
  });

  it("renders an archive-wide, searchable view of open proof obligations", async () => {
    const root = tmpDir("lax-site-proof-obligations-");
    const archive = [...submissions(), ...graphSubmissions()];
    // Unproven theorems and lemmas from registered submissions are listed.
    archive.find(({ record }) => record.id === "Lax4")!.output!.concepts[0]!.type = "theorem";
    archive.find(({ record }) => record.id === "Lax4")!.output!.concepts[1]!.type = "lemma";
    // Explicit open questions are listed even while their submission is a draft.
    const draft = archive.find(({ record }) => record.id === "Lax3")!;
    draft.record.state = "draft";
    draft.output!.concepts[0]!.type = "open question";
    draft.output!.concepts[0]!.statements = [{ id: "Lax3.Middle.open", signature: "open : True" }];
    // Other unproven statement types from drafts remain excluded.
    draft.output!.concepts.push({
      id: "Lax3.DraftTheorem", path: "concepts/Lax3/DraftTheorem.lean", title: "Draft theorem",
      type: "theorem", description: "", imports: [], sourceText: "",
      statements: [{ id: "Lax3.DraftTheorem.fact", signature: "fact : True" }],
    });
    // A grounded statement does not remain a proof obligation even if its
    // concept is still annotated as an open question.
    archive.find(({ record }) => record.id === "Lax2")!.output!.concepts[0]!.type = "open question";
    await generateSite(archive, root);
    const html = fs.readFileSync(path.join(root, "open-proof-obligations.html"), "utf8");

    expect(html).toContain("3 proof obligations · 3 open statements · 2 submissions");
    expect(html).toContain('placeholder="Search proof obligations"');
    expect(html).toContain('id="open-problems-list"');
    expect(html).toContain('data-type="open question"');
    expect(html).toContain('data-type="theorem"');
    expect(html).toContain('data-type="lemma"');
    expect(html).toContain('href="Lax4/Lax4.Top.html"');
    expect(html).toContain("Lax4.Top.a");
    expect(html).toContain('href="Lax4/Lax4.Aux.html"');
    expect(html).toContain("Lax4.Aux.b");
    expect(html).toContain("Lax3.Middle.open");
    expect(html).not.toContain("Lax3.DraftTheorem.fact");
    expect(html).not.toContain('href="Lax2/Lax2.C.html"');
    expect(html).not.toContain('href="Lax1/Lax1.Base.html"');
  });

  it("orders registered search results before drafts and indexes concept names", async () => {
    const make = (id: string, state: "draft" | "registered", title: string, conceptTitle: string): SiteSubmission => ({
      record: {
        specVersion: "1", id, state, createdAt: "2026-01-01T00:00:00Z", owners: [],
        ...(state === "registered" ? { registeredAt: "2026-01-02T00:00:00Z" } : {}),
      },
      output: {
        specVersion: "1", id,
        manifest: { specVersion: "1", id, leanVersion: "v4.30.0", mathlibVersion: "abc", title, authors: [], bibEntries: [] },
        abstract: "", requiredByConcepts: [], requiredByProofs: [], proofs: [],
        concepts: [{
          id: `${id}.C`, path: `concepts/${id}/C.lean`, title: conceptTitle, type: "definition",
          description: "", imports: [], sourceText: "", statements: [],
        }],
      },
    });
    const root = tmpDir("lax-site-search-");
    await generateSite([
      make("Lax1", "draft", "Draft title", "Topology"),
      make("Lax2", "registered", "Registered title", "Combinatorics"),
      make("Lax3", "draft", "Another draft", "Geometry"),
    ], root);
    const index = fs.readFileSync(path.join(root, "index.html"), "utf8");
    const entryList = index.slice(index.indexOf('<ul id="entry-list">'), index.indexOf("</ul>"));
    expect(index.indexOf('data-search-title="lax2 registered title"'))
      .toBeLessThan(index.indexOf('data-search-title="lax1 draft title"'));
    expect(index.indexOf('data-entry-group="registered">Registered</li>'))
      .toBeLessThan(index.indexOf('data-search-title="lax2 registered title"'));
    expect(index.indexOf('data-search-title="lax2 registered title"'))
      .toBeLessThan(index.indexOf('data-entry-group="draft">Work in Progress</li>'));
    expect(index.indexOf('data-entry-group="draft">Work in Progress</li>'))
      .toBeLessThan(index.indexOf('data-search-title="lax1 draft title"'));
    expect(index).toContain('data-search-concepts="lax2.c combinatorics definition"');
    expect(index).toContain('data-search-concepts="lax3.c geometry definition"');
    expect(entryList).toContain('<span class="entry-label"><span class="entry-label-text">Registered title</span></span>');
    expect(entryList).toContain('<span class="entry-label"><span class="entry-label-text">Draft title</span></span>');
    expect(entryList).toContain('<span class="entry-label"><span class="entry-label-text">Another draft</span></span>');
    expect(entryList).not.toContain('<span class="entry-id">');
    expect(index).not.toContain('class="draft-badge"');
  });

  it("renders the submission page: paper masthead, compact grids, citation, graph data", async () => {
    const root = tmpDir("lax-site-sub-");
    await generateSite(submissions(), root);
    const html = fs.readFileSync(path.join(root, "Lax2", "index.html"), "utf8");
    // paper masthead: the title stands alone; id and byline share the dim
    // metadata line before the abstract
    expect(html).toContain('<h1 class="paper-title">Two</h1>');
    expect(html).not.toContain('class="submission-title-id"');
    expect(html).not.toContain('class="submission-title-separator"');
    expect(html).not.toContain('class="paper-authors"');
    expect(html).toContain('<p class="paper-meta"><span class="submission-meta-id">Lax2</span><span class="meta-sep">·</span><span class="formalized-label">formalized by</span> <span class="paper-author"><a class="paper-author-name" href="https://orcid.org/0000-0002-1825-0097" target="_blank" rel="noopener noreferrer">Alice</a>');
    expect(html.indexOf('class="paper-meta"')).toBeLessThan(html.indexOf('class="katex"'));
    // the abstract is rendered under its own heading, not as an inline block
    expect(html).toContain("Abstract");
    expect(html).toContain('class="paper-abstract"');
    expect(html).toContain('href="https://github.com/alice"');
    const sourceTree = `https://github.com/example/math/tree/${"a".repeat(40)}/`;
    expect(html).toContain(`<a href="${sourceTree}" title="${sourceTree}"><code>GitHub @aaaaaaa</code></a>`);
    expect(html).not.toContain("github.com/example/math@aaaaaaa");
    expect(html).toContain("v4.30.0");
    // concepts: three-part compact entries; the page's own Lax2. prefix is
    // pruned from the display (full id stays in the tooltip and href)
    expect(html).toContain(">def</span>");
    expect(html).toContain(">thm✓</span>");
    expect(html).not.toContain('class="status-mark');
    expect(html).toContain('<a href="Lax2.C.html" title="Lax2.C"><code>C</code></a>');
    expect(html.indexOf('class="concept-list"')).toBeLessThan(html.indexOf('id="concept-dag"'));
    // Statements and definitions form separate grids, with no badge legend.
    expect(html).toMatch(/<ul class="concept-list" aria-label="Statements">\s*<li>[^]*?Lax2\.C\.html[^]*?<\/ul>\s*<ul class="concept-list" aria-label="Definitions">\s*<li>[^]*?Lax2\.D\.html[^]*?<\/ul>/);
    expect(html).not.toContain('class="badge-legend"');
    expect(html).not.toContain("letters abbreviate the concept's type");
    // judgment-card proof entry: head links to the proof page, the conclusion
    // is rendered as its claim-concept, annotation sections stay off this page
    expect(html).toContain('id="p-Lax2Proofs.truth"');
    expect(html).toContain('href="../Lax2/Lax2Proofs.truth.html"');
    // the proof marker is a boxed chip, parallel to the type badge
    expect(html).toContain('class="proof-badge"');
    expect(html).not.toContain("proof-item-turnstile");
    // the judgment card leads inside the shared white box, its surface links
    // to the proof page, and the description stays off the list
    expect(html).toContain('class="proof-list-box"');
    expect(html).toContain('<a class="judgment-overlay" href="../Lax2/Lax2Proofs.truth.html"');
    expect(html.indexOf('class="judgment-frame"')).toBeLessThan(html.indexOf('class="proof-item-head"'));
    // the description leaves the list (it stays in the graph JSON for the
    // proof-node tooltip and on the proof page itself)
    expect(html).not.toContain("proof-item-desc");
    expect(html).toContain('class="judgment"');
    expect(html).toContain("no assumptions");
    expect(html).toContain('class="claim-entry"');
    // judgment claims and the proof-id subline drop the page's own prefixes
    expect(html).toMatch(/judgment-conclusion[^]*?Lax2\.C\.html[^]*?<code>C<\/code>/);
    expect(html).toContain('title="Lax2Proofs.truth"><code>truth</code>');
    expect(html).not.toContain("Strategy");
    expect(html.indexOf('id="proof-network"')).toBeLessThan(html.indexOf('class="proof-list"'));
    expect(html).toMatch(/<details class="figure-details">\s*<summary>Proof list<\/summary>\s*<div class="proof-list-box">/);
    // both proof surfaces link out to the proof package — a tree link, since
    // `proofs/` is a directory, not the file the `path` argument means
    const proofsTree = `https://github.com/example/math/tree/${"a".repeat(40)}/proofs`;
    expect(html).toContain(`<p class="proof-list-source">Lean sources for these proofs: <a class="source-link" href="${proofsTree}">proofs/ on GitHub</a>`);
    expect(html).toContain(`<h4 class="figure-title">Proof network<a class="source-link" href="${proofsTree}">view on GitHub</a></h4>`);
    // citation for a registered submission has no draft note
    expect(html).toContain("@misc{Lax2");
    expect(html).toContain('<section class="page-section"><h3 class="section-title" id="citation">Cite this</h3>');
    expect(html).toContain('<pre class="citation" id="submission-citation">');
    expect(html).toContain('data-copy-citation aria-controls="submission-citation" aria-label="Copy BibTeX to clipboard"');
    expect(html).toContain('<output class="citation-copy-status" aria-live="polite"></output>');
    expect(html).toMatch(/<script src="\.\.\/assets\/citation\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(html).toContain('<section class="page-section discussion-section" aria-labelledby="discussion-title">');
    expect(html).toContain('class="page-reactions"');
    expect(html).toContain('data-reactions-url="https://laxarchive.org/Lax2/"');
    expect(html).toContain('data-review-kind="submission" data-source-lines="0"');
    expect(html).toContain('data-submission-concept-urls="');
    expect(html).toContain('data-submission-flagged-note hidden');
    expect(html).toContain('data-concept-review-progress');
    expect(html).toContain('data-concept-review-url="https://laxarchive.org/Lax2/Lax2.C.html" hidden');
    expect(html).toContain('data-reaction="endorse"');
    expect(html).toContain('data-reaction="flag"');
    expect(html).toContain('<span class="page-reaction-icon" aria-hidden="true">🥳</span><span>Endorse</span>');
    expect(html).toContain('<span class="page-reaction-icon" aria-hidden="true">🚩</span><span>Flag</span>');
    expect(html).not.toContain('data-reaction="like"');
    expect(html).not.toContain('data-reaction="dislike"');
    expect(html).not.toContain('data-reaction="rocket"');
    expect(html).toContain('data-reaction-voters="endorse"');
    expect(html).toContain('data-flag-list-open');
    expect(html).toContain('data-flag-list-dialog');
    expect(html).toContain('data-flag-editor');
    expect(html).toContain('data-flag-message rows="6" maxlength="2000" required');
    expect(html).toContain("Show people who endorse this submission");
    expect(html).toContain("What is wrong?");
    expect(html).not.toContain("Optional source annotation");
    expect(html).not.toContain("Was this page useful?");
    expect(html).not.toContain("Votes and voter names are public.");
    expect(html.indexOf('class="page-reactions"')).toBeLessThan(html.indexOf('class="paper-abstract"'));
    expect(html.indexOf('class="page-reactions"')).toBeLessThan(html.indexOf("discussion-section"));
    expect(html).toContain('data-remark42-url="https://laxarchive.org/Lax2/"');
    expect(html).toContain('class="remark42__counter" data-url="https://laxarchive.org/Lax2/"');
    expect(html).toMatch(/<p class="discussion-loading" id="remark42-status"[^>]*>[^]*?<\/p>\s*<div id="remark42"[^>]*><\/div>/);
    expect(html).not.toContain("your ORCID profile must share a public name.");
    expect(html).toMatch(/<script src="\.\.\/assets\/comments\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(html).toContain("script-src 'self' https://comments.laxarchive.org");
    expect(html).toContain("frame-src https://comments.laxarchive.org");
    expect(html).not.toContain("note = {draft}");
    expect(html).not.toContain("draft-banner");
    // inline JSON graph data parses and grays nothing (no external neighbors)
    const match = /<script type="application\/json" id="graph-data">(.*?)<\/script>/s.exec(html)!;
    const data = JSON.parse(match[1]!);
    expect(data.concepts.nodes.map((n: { id: string }) => n.id)).toEqual(["Lax2.C", "Lax2.D"]);
    expect(data.concepts.edges).toEqual([{ from: "Lax2.C", to: "Lax2.D" }]);
    expect(data.proofs.proofs[0]).toMatchObject({ id: "Lax2Proofs.truth", conclusion: "Lax2.C.truth", ext: false });
    // fill = status: concept nodes carry it; statement nodes display their
    // home concept, with the raw id kept for tooltips and the statement's
    // position inside that concept for the figure's docks
    expect(data.concepts.nodes.map((n: { id: string; status: string }) => [n.id, n.status]))
      .toEqual([["Lax2.C", "proven"], ["Lax2.D", "none"]]);
    expect(data.proofs.statements[0]).toMatchObject({
      id: "Lax2.C.truth", label: "Lax2.C", owner: "Lax2", proven: true, ext: false,
      concept: "Lax2.C", index: 1, count: 1,
    });
    // a single-statement archive shows no ordinals and no dock furniture
    expect(html).not.toContain("claim-ordinal");
    expect(html).not.toContain("legend-dock");
    // both figures share the legend grammar and a tooltip panel
    expect(html).toContain("legend-proof-chip");
    expect(html).toContain('class="legend-node fill-proven"');
    expect(html).toContain('class="legend-node stroke-own"');
    expect(html).toContain('<i class="legend-node fill-none"></i>Definition</span>');
    expect(html).not.toMatch(/nothing\s+to\s+prove/);
    expect((html.match(/class="graph-tooltip"/g) ?? []).length).toBe(2);
    // Only concept/proof figures get a large-window control; the submission
    // map deliberately remains an inline overview.
    expect((html.match(/data-graph-expand/g) ?? []).length).toBe(2);
    expect(html).toContain('data-graph-label="concept map" aria-expanded="false"');
    expect(html).toContain('data-graph-label="proof network" aria-expanded="false"');
    expect(html).toContain('<figure class="graph-figure proof-network-figure">');
    expect(html).toMatch(/<span class="proof-flow">assumptions <svg class="legend-assumptions"[^>]*>(<path[^>]*\/>){3}<\/svg><i class="legend-proof-chip" aria-hidden="true">⊢<\/i><svg class="legend-arrow legend-flow-arrow"[^>]*><path[^>]*\/><\/svg> conclusion<\/span>/);
    expect(html).not.toContain("click to open");
    expect(html).not.toContain('class="legend-note">assumptions');
  });

  it("shows only relevant legend items while preserving their global order", async () => {
    const root = tmpDir("lax-site-legends-");
    await generateSite([...submissions(), ...graphSubmissions()], root);
    const legend = (html: string, label: string, tag: "div" | "figcaption") => {
      const match = new RegExp(`<${tag}[^>]*aria-label="${label}"[^>]*>.*?</${tag}>`, "s").exec(html);
      expect(match, `${label} should be present`).not.toBeNull();
      return match![0];
    };
    const inOrder = (html: string, values: string[]) => {
      const positions = values.map((value) => html.indexOf(value));
      expect(positions.every((position) => position >= 0)).toBe(true);
      expect(positions).toEqual([...positions].sort((a, b) => a - b));
    };

    // Lax2 has a proven claim and a definition, but no open or external
    // concepts. Its one proof is grounded, local, and acyclic.
    const grounded = fs.readFileSync(path.join(root, "Lax2", "index.html"), "utf8");
    const groundedConcepts = legend(grounded, "Concept map legend", "figcaption");
    expect(groundedConcepts).toContain("fill-proven");
    expect(groundedConcepts).not.toContain("fill-open");
    expect(groundedConcepts).toContain("fill-none");
    expect(groundedConcepts).toContain("stroke-own");
    expect(groundedConcepts).not.toContain("stroke-ext");
    inOrder(groundedConcepts, ["fill-proven", "fill-none", "stroke-own", "legend-arrow"]);

    const groundedProofs = legend(grounded, "Proof network legend", "figcaption");
    expect(groundedProofs).toContain("fill-proven");
    expect(groundedProofs).not.toContain("fill-open");
    expect(groundedProofs).toContain("stroke-own");
    expect(groundedProofs).not.toContain("stroke-ext");
    expect(groundedProofs).not.toContain("legend-cycle");
    inOrder(groundedProofs, ["proof-flow", "fill-proven", "stroke-own", "⊢</i>Proof</span>"]);

    // Lax4's claims are open, its concept ancestry contains definitions from
    // other submissions, and its two proofs form a cycle.
    const cyclic = fs.readFileSync(path.join(root, "Lax4", "index.html"), "utf8");
    const cyclicConcepts = legend(cyclic, "Concept map legend", "figcaption");
    expect(cyclicConcepts).not.toContain("fill-proven");
    inOrder(cyclicConcepts, ["fill-open", "fill-none", "stroke-own", "stroke-ext", "legend-arrow"]);

    const cyclicProofs = legend(cyclic, "Proof network legend", "figcaption");
    expect(cyclicProofs).not.toContain("fill-proven");
    expect(cyclicProofs).not.toContain("stroke-ext");
    inOrder(cyclicProofs, ["proof-flow", "fill-open", "stroke-own", "⊢</i>Proof</span>", "legend-cycle"]);
  });

  it("emits expandable concept closures and proof readiness metadata for deterministic DAGs", async () => {
    const root = tmpDir("lax-site-graphs-");
    await generateSite([...submissions(), ...graphSubmissions()], root);
    const html = fs.readFileSync(path.join(root, "Lax4", "index.html"), "utf8");
    expect(html).toContain('data-concept-review-url="https://laxarchive.org/Lax4/Lax4.Top.html" hidden');
    // ancestors are on by default, descendants off — both closures run over
    // the whole archive, not just this submission
    expect(html).toContain('id="concept-expand"');
    expect(html).toContain("Hide ancestors");
    expect(html).toContain('data-graph="concepts" data-ancestry="true"');
    expect(html).toContain('id="concept-descend"');
    expect(html).toContain("Show descendants");
    expect(html).not.toContain('aria-controls="concept-dag" aria-pressed="false">Hide');
    // The concept map starts collapsed; the proof network remains visible.
    expect(html).toMatch(/<details class="figure-details">\s*<summary>Concept map<\/summary>\s*<figure class="graph-figure">/);
    expect(html).toContain('<h4 class="figure-title">Proof network</h4>');
    expect(html).not.toContain("graph-toolbar-title");
    expect(html).toContain("B builds on A");
    // one cycle notion — the grounded/ungrounded split is gone
    expect(html).toContain("legend-cycle");
    expect(html).not.toContain("Ungrounded");

    const match = /<script type="application\/json" id="graph-data">(.*?)<\/script>/s.exec(html)!;
    const data = JSON.parse(match[1]!);
    expect(data.concepts.nodes.map((node: { id: string; dir: string }) => [node.id, node.dir])).toEqual([
      ["Lax1.Base", "up"],
      ["Lax3.Middle", "up"],
      ["Lax4.Aux", "core"],
      ["Lax4.Top", "core"],
    ]);
    expect(data.concepts.edges).toEqual([
      { from: "Lax1.Base", to: "Lax3.Middle" },
      { from: "Lax3.Middle", to: "Lax4.Top" },
    ]);
    expect(data.proofs.statements.every((node: { proven: boolean }) => !node.proven)).toBe(true);
    expect(data.proofs.proofs).toEqual(expect.arrayContaining([
      expect.objectContaining({ id: "Lax4Proofs.a", owner: "Lax4", assumptionsProven: false, outstanding: 1, href: "../Lax4/Lax4Proofs.a.html" }),
      expect.objectContaining({ id: "Lax4Proofs.b", owner: "Lax4", assumptionsProven: false, outstanding: 1, href: "../Lax4/Lax4Proofs.b.html" }),
    ]));

    const conceptHtml = fs.readFileSync(path.join(root, "Lax4", "Lax4.Top.html"), "utf8");
    expect(conceptHtml).toMatch(/<details class="figure-details">\s*<summary>Concept map<\/summary>\s*<figure class="graph-figure concept-root-graph">/);
    expect(conceptHtml).toContain("This concept");
    expect(conceptHtml).toContain("Hide ancestors");
    expect(conceptHtml).toContain('data-graph="concepts" data-ancestry="true"');
    expect(conceptHtml.indexOf('id="concept-dag"')).toBeLessThan(conceptHtml.indexOf('class="block block-statement"'));
    expect(conceptHtml).toMatch(/<script src="\.\.\/assets\/layout\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(conceptHtml).toMatch(/<script src="\.\.\/assets\/dag\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect((conceptHtml.match(/data-graph-expand/g) ?? []).length).toBe(1);
    const conceptMatch = /<script type="application\/json" id="graph-data">(.*?)<\/script>/s.exec(conceptHtml)!;
    const conceptData = JSON.parse(conceptMatch[1]!);
    expect(conceptData.concepts.nodes.map((node: { id: string; ext: boolean; dir: string }) =>
      [node.id, node.ext, node.dir])).toEqual([
      ["Lax1.Base", true, "up"],
      ["Lax3.Middle", true, "up"],
      ["Lax4.Top", false, "core"],
    ]);
    expect(conceptData.concepts.edges).toEqual([
      { from: "Lax1.Base", to: "Lax3.Middle" },
      { from: "Lax3.Middle", to: "Lax4.Top" },
    ]);
    expect(conceptData.proofs).toEqual({ statements: [], proofs: [] });

    // a mid-chain concept tags its transitive importers for the toggle
    const middleHtml = fs.readFileSync(path.join(root, "Lax3", "Lax3.Middle.html"), "utf8");
    const middleMatch = /<script type="application\/json" id="graph-data">(.*?)<\/script>/s.exec(middleHtml)!;
    const middleData = JSON.parse(middleMatch[1]!);
    expect(middleData.concepts.nodes.map((node: { id: string; dir: string }) => [node.id, node.dir])).toEqual([
      ["Lax1.Base", "up"],
      ["Lax3.Middle", "core"],
      ["Lax4.Top", "down"],
    ]);

    const script = fs.readFileSync(path.join(root, "assets", "dag.js"), "utf8");
    expect(script).toContain("stronglyConnectedComponents");
    expect(script).not.toContain("forceSimulation");
    expect(script).not.toContain("svgEl(g, 'title')");
    expect(script).not.toContain("addEventListener('mousemove'");
    expect(script).toContain("markerUnits: 'userSpaceOnUse'");
    expect(script).toContain("orient: 'auto'");
    expect(script).toContain("protectedRankRoute");
    expect(script).toContain("routeDagEdge");
    expect(script).toContain("segmentIsClear");
    expect(script).toContain("MIN_ARC_SEPARATION");
    expect(script).toContain("sources.length === 1");
    expect(script).toContain("EDGE_BEND_RADIUS");
    expect(script).toContain(" Q${corner.x},${corner.y}");
    expect(script).toContain("graph-edge-casing");
    const layoutScript = fs.readFileSync(path.join(root, "assets", "layout.js"), "utf8");
    expect(layoutScript).toContain("optimizeOrdering");
    expect(layoutScript).toContain("removeRepeatedCrossings");
    expect(layoutScript).toContain("straightenDummyChains");
    expect(layoutScript).toContain("alignEdgeChains");
    expect(layoutScript).toContain("rankRoutes");
    expect(script).toContain("requestAnimationFrame(render)");
    expect(script).toContain("event.key !== 'Escape'");
  });

  it("reveals transitively used concepts from other submissions below the submission's own", async () => {
    const archive = graphSubmissions();
    const root = tmpDir("lax-site-used-concepts-");
    await generateSite(archive, root);
    const html = fs.readFileSync(path.join(root, "Lax4", "index.html"), "utf8");
    const ownStart = html.indexOf('<ul class="concept-list"');
    const usedStart = html.indexOf('<div class="concept-used-list"');
    const used = html.slice(usedStart, html.indexOf("</div>", usedStart));

    expect(usedStart).toBeGreaterThan(ownStart);
    expect(html).toContain('data-used-concepts-toggle aria-controls="used-concepts-list"');
    expect(used).toContain('href="../Lax1/Lax1.Base.html" title="Lax1.Base"><code>Lax1.Base</code></a>');
    expect(used).toContain('data-concept-review-url="https://laxarchive.org/Lax1/Lax1.Base.html" hidden');
    expect(used).toContain('href="../Lax3/Lax3.Middle.html" title="Lax3.Middle"><code>Lax3.Middle</code></a>');
    expect(used).not.toContain("Lax4.Top");
  });

  it("maps each submission's dependants and dependencies across the whole archive", async () => {
    const root = tmpDir("lax-site-submap-");
    const archive = graphSubmissions();
    archive[0]!.output!.manifest.title = "Foundational submission";
    await generateSite([...submissions(), ...archive], root);
    const mapOf = (id: string) => {
      const html = fs.readFileSync(path.join(root, id, "index.html"), "utf8");
      const match = /<script type="application\/json" id="graph-data">(.*?)<\/script>/s.exec(html)!;
      return { html, data: JSON.parse(match[1]!).submissions };
    };

    // The chain Lax1 → Lax3 → Lax4 is read off the concepts' imports; every
    // page sees the whole of it, in both directions.
    const top = mapOf("Lax4");
    expect(top.html).toContain('<h3 class="section-title">Related submissions</h3>');
    expect(top.html).toContain('<h4 class="figure-title">Submission map</h4>');
    expect(top.html).toContain('id="submission-dag"');
    expect(top.html).toContain("Submission map legend");
    const reviewDependencies = /data-submission-concept-urls="([^"]+)"/.exec(top.html)?.[1] ?? "";
    const visibleReviewConcepts = /data-concept-review-urls="([^"]+)"/.exec(top.html)?.[1] ?? "";
    expect(reviewDependencies).toContain("https://laxarchive.org/Lax1/Lax1.Base.html");
    expect(reviewDependencies).toContain("https://laxarchive.org/Lax3/Lax3.Middle.html");
    expect(reviewDependencies).toContain("https://laxarchive.org/Lax4/Lax4.Top.html");
    expect(visibleReviewConcepts).toContain("Lax1.Base.html");
    expect(visibleReviewConcepts).toContain("Lax3.Middle.html");
    expect(top.data.nodes.map((n: { id: string; dir: string }) => [n.id, n.dir]))
      .toEqual([["Lax1", "up"], ["Lax3", "up"], ["Lax4", "core"]]);
    expect(top.data.edges).toEqual([
      { from: "Lax1", to: "Lax3", kind: "concepts" },
      { from: "Lax3", to: "Lax4", kind: "concepts" },
    ]);
    // Concept dependencies throughout, so the legend names only that arrow.
    expect(top.html).toContain("B's concepts build on A");
    expect(top.html).not.toContain("only B's proofs build on A");
    expect(top.data.nodes[0]).toMatchObject({ href: "../Lax1/index.html", title: "Foundational submission", state: "registered", concepts: 1, proofs: 0, ext: true });

    const dagScript = fs.readFileSync(path.join(root, "assets", "dag.js"), "utf8");
    expect(dagScript).toContain("labelOf: (node) => node.title");
    expect(dagScript).toContain("labelOf: (node) => node.title || 'Untitled concept'");
    expect(dagScript).not.toContain("['Concept', node.id]");

    const base = mapOf("Lax1");
    expect(base.data.nodes.map((n: { id: string; dir: string }) => [n.id, n.dir]))
      .toEqual([["Lax1", "core"], ["Lax3", "down"], ["Lax4", "down"]]);
    const middle = mapOf("Lax3");
    expect(middle.data.nodes.map((n: { id: string; dir: string }) => [n.id, n.dir]))
      .toEqual([["Lax1", "up"], ["Lax3", "core"], ["Lax4", "down"]]);

    // An unrelated submission gets a sentence, not an empty figure.
    const lone = mapOf("Lax2");
    expect(lone.data.nodes.map((n: { id: string }) => n.id)).toEqual(["Lax2"]);
    expect(lone.html).toContain("builds on this one, and this one builds on none");
    expect(lone.html).not.toContain('id="submission-dag"');
  });

  it("counts a declared package require as a dependency even with nothing importing it", () => {
    const all = [...submissions(), ...graphSubmissions()];
    // Lax2 requires Lax1's packages without importing a single concept.
    all[0]!.output!.requiredByConcepts = ["Lax1"];
    all[0]!.output!.requiredByProofs = ["Lax1Proofs", "mathlib"];
    const model = new SiteModel(all);
    expect([...model.submissionUses.get("Lax2")!]).toEqual([["Lax1", "concepts"]]);
    expect(model.submissionDownstream("Lax1")).toEqual(["Lax2", "Lax3", "Lax4"]);
    // "mathlib" is not a submission and never becomes a node
    expect(model.submissionById.has("mathlib")).toBe(false);
  });

  it("labels a require only the proof package declares as a proof dependency", () => {
    const all = [...submissions(), ...graphSubmissions()];
    // Lax2's concepts stand alone; only its proofs reach for Lax1's proofs.
    all[0]!.output!.requiredByProofs = ["Lax1Proofs"];
    const model = new SiteModel(all);
    expect([...model.submissionUses.get("Lax2")!]).toEqual([["Lax1", "proofs"]]);
    expect([...model.submissionUsedBy.get("Lax1")!]).toContainEqual(["Lax2", "proofs"]);
    // A concept-level require on the same target wins: the statements
    // themselves already rest on Lax1, so the proof half says nothing more.
    all[0]!.output!.requiredByConcepts = ["Lax1"];
    expect([...new SiteModel(all).submissionUses.get("Lax2")!]).toEqual([["Lax1", "concepts"]]);
  });

  it("resolves a package require whose spelling differs from the submission id", () => {
    const all = graphSubmissions();
    // Records are keyed `lax-1`, lakefiles name the package `Lax1Proofs`.
    for (const submission of all) {
      submission.record.id = submission.record.id.replace(/^Lax/, "lax-");
      submission.output!.id = submission.record.id;
    }
    all[2]!.output!.requiredByProofs = ["Lax1Proofs"];
    const model = new SiteModel(all);
    expect([...model.submissionUses.get("lax-4")!]).toContainEqual(["lax-1", "proofs"]);
  });

  it("draws a proof-only dependency as its own edge and names it in the legend", async () => {
    const root = tmpDir("lax-site-proofdep-");
    const all = [...submissions(), ...graphSubmissions()];
    all[0]!.output!.requiredByProofs = ["Lax1Proofs"];
    await generateSite(all, root);
    const html = fs.readFileSync(path.join(root, "Lax2", "index.html"), "utf8");
    const data = JSON.parse(
      /<script type="application\/json" id="graph-data">(.*?)<\/script>/s.exec(html)![1]!,
    ).submissions;
    expect(data.edges).toContainEqual({ from: "Lax1", to: "Lax2", kind: "proofs" });
    expect(html).toContain("only B's proofs build on A");
    const script = fs.readFileSync(path.join(root, "assets", "dag.js"), "utf8");
    expect(script).toContain("edge.kind === 'proofs' ? ' proof-dep' : ''");
    const css = fs.readFileSync(path.join(root, "assets", "style.css"), "utf8");
    expect(css).toContain(".dag-edge.proof-dep{ stroke: var(--proof-dep)");
  });

  it("renders the concept page: type heading, tinted source, sections, deps", async () => {
    const root = tmpDir("lax-site-concept-");
    await generateSite(submissions(), root);
    const html = fs.readFileSync(path.join(root, "Lax2", "Lax2.C.html"), "utf8");
    // NL block headed by the capitalized type
    expect(html).toContain("<h3>Theorem</h3>");
    // line-numbered source with the proven statement lines tinted
    expect(html.match(/<tr id="L\d+"/g)).toHaveLength(4);
    expect(html).toContain("line-proven");
    expect(html).toContain("github.com/example/math/blob/" + "a".repeat(40) + "/concepts/Lax2/C.lean");
    // extra annotation section as its own block
    expect(html).toContain("<h3>Review notes</h3>");
    // statement links now land on the source line; individual cards are gone
    expect(html).toContain('id="s-Lax2.C.truth"');
    // The proof action floats over the source block at the declaration row,
    // while staying outside the horizontally scrolling table itself.
    const docRow = html.match(/<tr id="L2"[^]*?<\/tr>/)?.[0] ?? "";
    const axiomRow = html.match(/<tr id="L3"[^]*?<\/tr>/)?.[0] ?? "";
    expect(docRow).not.toContain("statement-proof-button");
    expect(axiomRow).not.toContain("statement-proof-button");
    expect(html).toContain('class="source-proof-rail" data-source-line="L3"');
    expect(html).toContain('class="statement-proof-button" href="https://github.com/example/math/blob/'
      + "a".repeat(40) + '/proofs/Lax2Proofs/Basic.lean"');
    expect(html).toContain('aria-label="View proof Lax2Proofs.truth on GitHub"');
    expect(html).toContain('class="statement-proof-label">Show Proof</span>');
    expect(html.indexOf('class="statement-proof-button"')).toBeGreaterThan(html.indexOf('class="inline-contract-shell"'));
    expect(html).toMatch(/<script src="\.\.\/assets\/source-proof\.js\?v=[a-f0-9]+"><\/script>/);
    expect(html).not.toContain('class="statement"');
    expect(html).not.toContain('block-statements');
    expect(html).toContain("mathlib4_docs/Mathlib/Data/Nat/Basic.html");
    expect(html).toContain(">proven</span>");
    expect(html).toContain('<details class="deps-col block-details"><summary>Builds on</summary>');
    expect(html).toContain('<details class="deps-col block-details"><summary>Used by</summary>');
    expect(html).toContain('<details class="deps-col block-details"><summary>From Mathlib</summary>');
    expect(html).not.toContain("<h3>Imported</h3>");
    expect(html).not.toContain("Mathlib imports");
    // the claim's evidence block lists the archived proof, linking to its page
    expect(html).toContain("<h3>Evidence</h3>");
    expect(html).toContain('href="../Lax2/Lax2Proofs.truth.html"');
    expect(html).toContain('data-remark42-url="https://laxarchive.org/Lax2/Lax2.C.html"');
    expect(html).toContain('data-reactions-url="https://laxarchive.org/Lax2/Lax2.C.html"');
    expect(html).toContain('data-review-kind="concept" data-source-lines="4"');
    expect(html).toContain('data-source-review-rails aria-label="Source flags"');
    expect(html).toContain('<input type="hidden" data-flag-line>');
    expect(html).not.toContain('data-flag-line-start');
    expect(html).not.toContain('data-flag-line-end');
    expect(html).toContain('data-flag-line-picker>Choose from source');
    expect(html.indexOf('class="page-reactions"')).toBeLessThan(html.indexOf("concept-root-graph"));
    expect(html.indexOf('class="page-reactions"')).toBeLessThan(html.indexOf("discussion-section"));
    expect(html).toMatch(/<script src="\.\.\/assets\/comments\.js\?v=[0-9a-f]{12}"><\/script>/);
    // The graph is rooted at C; its importer D rides along behind the
    // descendants toggle (hidden until pressed).
    const graphMatch = /<script type="application\/json" id="graph-data">(.*?)<\/script>/s.exec(html)!;
    expect(JSON.parse(graphMatch[1]!).concepts.nodes.map((node: { id: string; dir: string }) => [node.id, node.dir]))
      .toEqual([["Lax2.C", "core"], ["Lax2.D", "down"]]);
    expect(html).not.toContain('class="concept-id"');
    expect(html).toContain('<a class="sidebar-back" href="../Lax2/index.html"');
    // sidebar highlights the active concept; the NL heading is the type
    expect(html).toContain('class="active"');
    const untyped = fs.readFileSync(path.join(root, "Lax2", "Lax2.D.html"), "utf8");
    expect(untyped).toContain("<h3>Definition</h3>");
    expect(untyped).toContain('class="status-pill pill-none">definition</span>');
    expect(untyped).not.toMatch(/nothing\s+to\s+prove/);
    expect(untyped).toContain("Used by");
    // a definition-concept claims nothing, so it carries no evidence block
    expect(untyped).not.toContain("<h3>Evidence</h3>");
  });

  it("renders inline and display math inside Lean source comments only", async () => {
    const authored = submissions();
    const concept = authored[0]!.output!.concepts[0]!;
    concept.sourceText = String.raw`namespace Lax2.C
/-!
Inline $x^2$ in a module comment.
$$
  \sum_{i=1}^n i
$$
-/
-- Line comment math $z_i$ and native Lean math $⊥$.
def literal := "$not_math$"
axiom truth : True
end Lax2.C`;
    concept.statements[0]!.startLine = 10;
    concept.statements[0]!.endLine = 10;

    const root = tmpDir("lax-site-source-math-");
    await generateSite(authored, root);
    const html = fs.readFileSync(path.join(root, "Lax2", "Lax2.C.html"), "utf8");
    const tableStart = html.indexOf('<table class="inline-contract-table">');
    const source = html.slice(tableStart, html.indexOf("</table>", tableStart));

    expect(source.match(/<tr id="L\d+"/g)).toHaveLength(11);
    expect((source.match(/class="katex"/g) ?? []).length).toBe(4);
    expect((source.match(/source-math-inline/g) ?? []).length).toBe(3);
    expect((source.match(/source-math-display/g) ?? []).length).toBe(1);
    expect(source).toContain('class="katex-display"');
    expect(source).toContain("$not_math$");
    expect(source).not.toContain("$x^2$");
    expect(source).not.toContain("$z_i$");
    expect(source).not.toContain("$⊥$");
    expect(source).not.toContain("$$");
    expect(source).not.toContain("LAXSOURCEMATHTOKEN");
  });

  it("links resolved archive identifiers in Lean code", async () => {
    const authored = submissions();
    authored[0]!.output!.concepts[0]!.sourceText = [
      authored[0]!.output!.concepts[0]!.sourceText,
      "def ImportedThing : Type := Nat",
      "-- def CommentOnly : Type := Nat",
      'def declarationLabel := "def StringOnly : Type := Nat"',
    ].join("\n");
    authored[0]!.output!.concepts[1]!.sourceText = [
      "import Lax2.C",
      "#check Lax2.C.truth",
      "namespace Lax2.D",
      "axiom local_truth (x : ImportedThing) : True",
      "end Lax2.D",
      "#check CommentOnly",
      "#check StringOnly",
      "-- Lax2.C.truth is prose here",
      'def label := "Lax2.C"',
      "#check Lax999.Unknown",
    ].join("\n");
    authored[0]!.output!.concepts[1]!.statements = [{
      id: "Lax2.D.local_truth",
      signature: "local_truth : True",
      startLine: 4,
      endLine: 4,
    }];

    const root = tmpDir("lax-site-source-links-");
    await generateSite(authored, root);
    const html = fs.readFileSync(path.join(root, "Lax2", "Lax2.D.html"), "utf8");
    const tableStart = html.indexOf('<table class="inline-contract-table">');
    const source = html.slice(tableStart, html.indexOf("</table>", tableStart));

    const linked = [...source.matchAll(/<a class="lean-identifier-link" href="([^"]+)">([^]*?)<\/a>/g)]
      .map((match) => ({ href: match[1], name: match[2]!.replace(/<[^>]*>/g, "") }));
    expect(linked).toContainEqual({ href: "../Lax2/Lax2.C.html", name: "Lax2.C" });
    expect(linked).toContainEqual({ href: "../Lax2/Lax2.C.html#s-Lax2.C.truth", name: "Lax2.C.truth" });
    expect(linked.map((link) => link.name)).not.toContain("local_truth");
    // This definition was explicitly declared in the root namespace.
    expect(linked).toContainEqual({ href: "../Lax2/Lax2.C.html#L5", name: "ImportedThing" });
    expect(source).toContain("CommentOnly");
    expect(source).toContain("StringOnly");
    expect(source).not.toContain('href="../Lax2/Lax2.C.html">CommentOnly</a>');
    expect(source).not.toContain('href="../Lax2/Lax2.C.html">StringOnly</a>');
    expect(source).toContain("-- Lax2.C.truth is prose here");
    expect(source).toContain("&quot;Lax2.C&quot;");
    expect(source).toContain("Lax999.Unknown");
    expect(source).not.toContain("LAXSOURCELINKTOKEN");
  });

  it("renders proof pages: judgment card, status pill, annotation sections", async () => {
    const root = tmpDir("lax-site-proof-");
    await generateSite([...submissions(), ...graphSubmissions()], root);
    const html = fs.readFileSync(path.join(root, "Lax2", "Lax2Proofs.truth.html"), "utf8");
    expect(html).toContain("Lax2Proofs.truth");
    expect(html).toContain('<h1 class="concept-title">Proof of <span class="proof-concept-title">`Truth`</span></h1>');
    expect(html).toMatch(/class="concept-microline proof-microline"[^]*?class="status-pills"[^]*?>grounded<\/span>[^]*?proofs\/Lax2Proofs\/Basic\.lean/);
    expect(html.match(/<p class="concept-microline proof-microline">[^]*?<\/p>/)?.[0]).not.toContain("proof-badge");
    expect(html).toContain('data-tooltip="No open assumptions remain in the archive: every dependency is backed by a checked proof, ultimately reducing to Lean and Mathlib."');
    expect(html).not.toContain('class="concept-id proof-name"');
    expect(html).toContain('class="judgment"');
    expect(html).toContain("no assumptions");
    expect(html).toMatch(/judgment-conclusion[^]*?Lax2\.C\.html[^]*?<code>C<\/code>/);
    expect(html).toContain(">grounded</span>");
    // the annotation body finally has a home: description and sections render
    expect(html).toContain("The direct proof.");
    expect(html).toContain("<h3>Strategy</h3>");
    // the page shows no Lean, so the way to the code is a button, not a
    // microline link: it deep-links the proof's own file
    expect(html).toContain('class="source-button" href="https://github.com/example/math/blob/'
      + "a".repeat(40) + '/proofs/Lax2Proofs/Basic.lean"');
    expect(html).toContain("Read the Lean proof on GitHub");
    const githubProof = "https://github.com/example/math/blob/" + "a".repeat(40) + "/proofs/Lax2Proofs/Basic.lean";
    expect(html).toContain(`<a href="${githubProof}"><code>proofs/Lax2Proofs/Basic.lean</code></a> · <a href="index.html">Lax2</a>`);
    // sidebar backs to the submission, not the archive index
    expect(html).toContain('<a class="sidebar-back" href="../Lax2/index.html"');
    // a proof with open assumptions is conditional
    const cyclic = fs.readFileSync(path.join(root, "Lax4", "Lax4Proofs.a.html"), "utf8");
    expect(cyclic).toContain("conditional — 1 open assumption");
    expect(cyclic).toMatch(/judgment-assumptions[^]*?Lax4\.Aux\.html[^]*?<code>Aux<\/code>/);
    // the sidebar marks the proof itself active
    expect(cyclic).toMatch(/<li class="active" data-type="proof"[^]*?Lax4Proofs\.a\.html/);
  });

  it("gives the sidebar status badges and a proofs group below the concepts", async () => {
    const root = tmpDir("lax-site-sidebar-");
    await generateSite(submissions(), root);
    const html = fs.readFileSync(path.join(root, "Lax2", "index.html"), "utf8");
    const sidebar = html.slice(html.indexOf('<aside id="sidebar">'), html.indexOf("</aside>"));
    // concepts carry the same status marks as the concept list: proven ✓ for
    // the theorem and the definition with their corresponding badge styles
    expect(sidebar).toMatch(/data-type="theorem"[^]*?type-badge proven[^]*?thm✓/);
    expect(sidebar).toMatch(/data-type="definition"[^]*?<span class="type-badge"[^]*?def</);
    expect(sidebar).toContain('<span class="entry-label-text">Truth</span>');
    expect(sidebar).toContain('<span class="entry-label-text">Definition helper</span>');
    // the proofs group follows the concepts, ⊢-chipped, prefix-pruned,
    // filterable as its own type
    expect(sidebar.indexOf(">Concepts</li>")).toBeLessThan(sidebar.indexOf(">Proofs</li>"));
    expect(sidebar).toMatch(/data-type="proof"[^]*?proof-badge[^]*?>truth</);
    expect(sidebar).toContain('<option value="proof">proof</option>');
  });

  it("keeps lemma review badges but excludes local and referenced lemmas from progress", async () => {
    const values = graphSubmissions();
    const externalLemma = values[1]!.output!.concepts.find((concept) => concept.id === "Lax3.Middle")!;
    const localLemma = values[2]!.output!.concepts.find((concept) => concept.id === "Lax4.Aux")!;
    externalLemma.type = "lemma";
    localLemma.type = "lemma";
    const root = tmpDir("lax-site-review-progress-lemmas-");
    await generateSite(values, root);

    const html = fs.readFileSync(path.join(root, "Lax4", "index.html"), "utf8");
    const progress = html.match(/<div class="concept-review-progress"[^>]+>/)?.[0] ?? "";
    expect(progress).toContain("Lax4.Top.html");
    expect(progress).toContain("Lax1.Base.html");
    expect(progress).not.toContain("Lax4.Aux.html");
    expect(progress).not.toContain("Lax3.Middle.html");
    expect(html).toContain('data-concept-review-url="https://laxarchive.org/Lax4/Lax4.Aux.html" hidden');
    expect(html).toContain('data-concept-review-url="https://laxarchive.org/Lax3/Lax3.Middle.html" hidden');
    expect(html).toContain('data-concept-review-url="https://laxarchive.org/Lax1/Lax1.Base.html" hidden');
    expect(html).toMatch(/data-submission-concept-urls="[^"]*Lax4\.Aux\.html/);
    expect(html).toMatch(/data-submission-concept-urls="[^"]*Lax3\.Middle\.html/);
  });

  it("omits review progress when a submission lists only lemmas", async () => {
    const values = submissions();
    values[0]!.output!.concepts.forEach((concept) => { concept.type = "lemma"; });
    const root = tmpDir("lax-site-review-progress-only-lemmas-");
    await generateSite(values, root);

    const html = fs.readFileSync(path.join(root, "Lax2", "index.html"), "utf8");
    expect(html).not.toContain("data-concept-review-progress");
    expect(html).toContain('data-concept-review-url="https://laxarchive.org/Lax2/Lax2.C.html" hidden');
    expect(html).toContain('data-concept-review-url="https://laxarchive.org/Lax2/Lax2.D.html" hidden');
  });

  it("compiles references instead of printing BibTeX, keeping unparseable entries raw", async () => {
    const authored = submissions();
    authored[0]!.output!.manifest.bibEntries.splice(1, 0, String.raw`@article{math-ref,
  author = {Noether, Emmy},
  title = {A {$K_t$}-minor bound for \ensuremath{\operatorname{tw}(G) \ge k}},
  journal = {Graphs of \(H\)-free classes},
  note = {Valid as $$n \to \infty$$},
  year = {2025},
}`);
    const root = tmpDir("lax-site-refs-");
    await generateSite(authored, root);
    const html = fs.readFileSync(path.join(root, "Lax2", "index.html"), "utf8");
    expect(html).toContain('<ol class="reference-list">');
    expect(html).toContain('<li id="ref-demo">');
    expect(html).toContain("Jane Doe and Hans Müller.");
    expect(html).toContain('<span class="reference-title">A Cited Result</span>.');
    expect(html).toContain("J. Math 1(2):3–4,");
    expect(html).toContain('<a href="https://doi.org/10.1000/demo">doi:10.1000/demo</a>');
    const mathReference = html.slice(html.indexOf('<li id="ref-math-ref">'), html.indexOf("</li>", html.indexOf('<li id="ref-math-ref">')));
    expect((mathReference.match(/class="katex"/g) ?? []).length).toBe(4);
    expect(mathReference).toContain('<span class="reference-title">A <span class="katex"');
    expect(mathReference).toContain('Graphs of <span class="katex"');
    expect(mathReference).not.toContain("$K_t$");
    expect(mathReference).not.toContain("\\ensuremath");
    expect(mathReference).not.toContain("\\(H\\)");
    expect(mathReference).not.toContain("$$");
    expect(mathReference).not.toContain('class="katex-display"');
    // the field-less @book{x} cannot be compiled and stays verbatim
    expect(html).toContain('<pre class="bib-entry">@book{x}</pre>');
  });

  it("fails fast on statements without a home and on typeless concepts", async () => {
    const broken = submissions();
    broken[0]!.output!.proofs[0]!.assumptions = ["Nobody.here"];
    await expect(generateSite(broken, tmpDir("lax-site-nohome-"))).rejects.toThrow(
      "statement Nobody.here has no home concept",
    );
    const typeless = submissions();
    delete typeless[0]!.output!.concepts[1]!.type;
    await expect(generateSite(typeless, tmpDir("lax-site-typeless-"))).rejects.toThrow(
      "concept Lax2.D declares no type",
    );
  });

  it("keeps outputless records and drafts citable and grouped as work in progress", async () => {
    const draft = submissions();
    draft[0]!.record.state = "draft";
    delete draft[0]!.record.registeredAt;
    const root = tmpDir("lax-site-draft-");
    await generateSite(draft, root);
    const html = fs.readFileSync(path.join(root, "Lax2", "index.html"), "utf8");
    expect(html).toContain("draft-banner");
    expect(html.indexOf("draft-banner")).toBeLessThan(html.indexOf("paper-head"));
    expect(html).not.toContain("state-draft");
    expect(html).toContain("@misc{Lax2");
    expect(html).toContain("note = {draft}");
    const concept = fs.readFileSync(path.join(root, "Lax2", "Lax2.C.html"), "utf8");
    expect(concept.indexOf("draft-banner")).toBeLessThan(concept.indexOf("concept-heading"));
    const index = fs.readFileSync(path.join(root, "index.html"), "utf8");
    const entryList = index.slice(index.indexOf('<ul id="entry-list">'), index.indexOf("</ul>"));
    expect(index).toContain('data-entry-group="draft">Work in Progress</li>');
    expect(index).not.toContain('data-entry-group="registered">Registered</li>');
    expect(index).toContain('<span class="entry-label"><span class="entry-label-text">Two</span></span>');
    expect(index).not.toContain('class="draft-badge"');
    expect(entryList).not.toContain('<span class="entry-id">Lax2</span>');
    const placeholder = fs.readFileSync(path.join(root, "Lax10", "index.html"), "utf8");
    expect(placeholder).toContain("No content uploaded yet");
  });
});

describe("supersedes version chains", () => {
  const make = (
    id: string,
    state: "registered" | "draft",
    title: string,
    supersedes?: string,
  ): SiteSubmission => {
    const number = Number(id.match(/\d+/)?.[0] ?? 1);
    const createdDay = String(number % 20 + 1).padStart(2, "0");
    const registeredDay = String(number % 20 + 2).padStart(2, "0");
    return {
      record: {
        specVersion: "1", id, state, createdAt: `2026-01-${createdDay}T00:00:00Z`,
        ...(state === "registered" ? { registeredAt: `2026-01-${registeredDay}T00:00:00Z` } : {}),
        source: {
          repository: "https://github.com/example/formalization",
          commit: String(number).repeat(40).slice(0, 40),
          folder: `submission-${number}`,
        },
      },
      output: {
        specVersion: "1", id,
        manifest: {
          specVersion: "1", id, leanVersion: `v4.${30 + number}.0`, mathlibVersion: `mathlib-${id}-abcdef`, title,
          authors: [], bibEntries: [], ...(supersedes ? { supersedes } : {}),
        },
        abstract: "An abstract.", requiredByConcepts: [], requiredByProofs: [],
        concepts: [{
          id: `${id.replace(/\W/g, "")}.C`, path: "concepts/C.lean", title: "C",
          type: "definition", description: "d", imports: [], mathlibImports: [],
          sourceText: "-- lean\n", statements: [],
        }],
        proofs: [],
      },
    };
  };
  const archive = () => [
    make("lax-1", "registered", "Old Result"),
    make("lax-2", "registered", "Middle Result", "lax-1"),
    make("lax-3", "registered", "Current Result", "lax-2"),
    make("lax-4", "draft", "Proposed Result", "lax-3"),
  ];

  it("binds only registered successors and walks chains both ways", () => {
    const model = new SiteModel(archive());
    expect(model.isSuperseded("lax-1")).toBe(true);
    expect(model.isSuperseded("lax-2")).toBe(true);
    // the draft's claim is recorded but does not bind
    expect(model.isSuperseded("lax-3")).toBe(false);
    expect(model.supersedesClaim.get("lax-4")).toBe("lax-3");
    expect(model.draftSuccessors.get("lax-3")).toEqual(["lax-4"]);
    expect(model.latestVersion("lax-1")).toBe("lax-3");
    expect(model.latestVersion("lax-2")).toBe("lax-3");
    expect(model.versionChain("lax-1")).toEqual(["lax-1", "lax-2", "lax-3"]);
    expect(model.versionChain("lax-2")).toEqual(["lax-1", "lax-2", "lax-3"]);
    expect(model.versionChain("lax-3")).toEqual(["lax-1", "lax-2", "lax-3"]);
    expect(model.versionChain("lax-4")).toEqual(["lax-4"]);
    expect(model.versionHistory("lax-3")).toEqual(["lax-1", "lax-2", "lax-3", "lax-4"]);
    expect(model.versionHistory("lax-4")).toEqual(["lax-1", "lax-2", "lax-3", "lax-4"]);
    expect(model.currentVersion("lax-1")).toBe("lax-3");
    expect(model.currentVersion("lax-2")).toBe("lax-3");
    expect(model.currentVersion("lax-4")).toBe("lax-3");
  });

  it("shows the full chain and its metadata in a prominent version dialog", async () => {
    const root = tmpDir("lax-site-versions-");
    await generateSite(archive(), root);

    const oldPage = fs.readFileSync(path.join(root, "lax-1", "index.html"), "utf8");
    expect(oldPage).toContain('class="version-notice version-notice-superseded"');
    expect(oldPage).toContain("<strong>Outdated version.</strong>");
    expect(oldPage).not.toContain("<strong>Superseded version.</strong>");
    expect(oldPage).toContain("The current version is");
    expect(oldPage).toContain('href="../lax-3/index.html?version=lax-3"');
    expect(oldPage).toContain('data-version-dialog');
    expect(oldPage).toContain('data-version-dialog-open');
    expect(oldPage).not.toContain('class="paper-version-button"');
    expect(oldPage).toContain('href="../lax-2/index.html?version=lax-2"');
    expect(oldPage).toContain("current version");
    expect(oldPage).toContain("viewing");
    expect(oldPage).toContain("Created</b>");
    expect(oldPage).toContain("Registered</b>");
    expect(oldPage).toContain("Lean</b> <code>v4.33.0</code>");
    expect(oldPage).toContain("mathlib</b> <code>mathlib-lax-3-abcdef</code>");
    expect(oldPage).toContain("GitHub source");
    expect(oldPage).toContain("https://github.com/example/formalization/tree/3333333333333333333333333333333333333333/submission-3");
    expect(oldPage).toContain("note = {superseded by lax-3}");
    expect(oldPage.indexOf('class="version-notice')).toBeLessThan(oldPage.indexOf('class="paper-head"'));
    const notice = oldPage.slice(oldPage.indexOf('class="version-notice'), oldPage.indexOf("</aside>", oldPage.indexOf('class="version-notice')));
    expect(notice).toContain('href="../lax-3/index.html?version=lax-3"><span class="submission-meta-id">lax-3</span></a>');
    expect(notice).not.toContain("Current Result");

    const oldConcept = fs.readFileSync(path.join(root, "lax-1", "lax1.C.html"), "utf8");
    expect(oldConcept).toContain('class="version-notice version-notice-superseded"');
    expect(oldConcept).toContain('href="../lax-3/index.html?version=lax-3"');
    expect(oldConcept).toContain("assets/version-history.js");

    const middlePage = fs.readFileSync(path.join(root, "lax-2", "index.html"), "utf8");
    expect(middlePage).toContain('class="version-notice version-notice-superseded"');
    expect(middlePage).toContain('href="../lax-3/index.html?version=lax-3"');
    expect(middlePage).toContain('class="version-item version-selected"');

    const currentPage = fs.readFileSync(path.join(root, "lax-3", "index.html"), "utf8");
    expect(currentPage).toContain('class="version-notice version-notice-pending"');
    expect(currentPage).toContain("<strong>New version in progress.</strong>");
    expect(currentPage).toContain("This remains the current registered version.");
    expect(currentPage).toContain('href="../lax-4/index.html?version=lax-4"');
    expect(currentPage).not.toContain('class="paper-version-button"');
    expect(currentPage).toContain("View 4 versions");
    expect(currentPage).toContain('data-version-dialog');
    expect(currentPage).toContain('href="../lax-1/index.html?version=lax-1"');
    expect(currentPage).toContain('href="../lax-2/index.html?version=lax-2"');
    expect(currentPage).toContain("version-mark-latest");
    expect(currentPage).toContain("version-mark-viewing");
    expect(currentPage).not.toContain("note = {superseded");

    const currentConcept = fs.readFileSync(path.join(root, "lax-3", "lax3.C.html"), "utf8");
    expect(currentConcept).toContain('class="version-notice version-notice-pending"');
    expect(currentConcept).toContain('href="../lax-4/index.html?version=lax-4"');

    const draftPage = fs.readFileSync(path.join(root, "lax-4", "index.html"), "utf8");
    expect(draftPage).toContain("<strong>Proposed new version.</strong>");
    expect(draftPage).toContain('href="../lax-3/index.html?version=lax-3"');
    expect(draftPage).toContain("View 4 versions");
    expect(draftPage).toContain("version-mark-draft");
    expect(draftPage).toContain('href="../lax-1/index.html?version=lax-1"');
  });

  it("ignores self and unknown targets and breaks stale double-claims deterministically", () => {
    const model = new SiteModel([
      make("lax-1", "registered", "Old"),
      make("lax-2", "registered", "A", "lax-1"),
      make("lax-6", "registered", "B", "lax-1"),
      make("lax-4", "registered", "Selfish", "lax-4"),
      make("lax-5", "registered", "Dangling", "lax-99"),
    ]);
    expect(model.supersedesClaim.has("lax-4")).toBe(false);
    expect(model.supersedesClaim.has("lax-5")).toBe(false);
    // the control plane admits one registered successor; stale data with two
    // resolves to the lowest id, deterministically
    expect(model.supersededBy.get("lax-1")).toBe("lax-2");
    expect(model.versionChain("lax-1")).toEqual(["lax-1", "lax-2"]);
  });

  it("carries the version dialog onto proof pages and output-less registered pages", async () => {
    const old = make("lax-1", "registered", "Old Result");
    old.output!.concepts[0]!.type = "theorem";
    old.output!.concepts[0]!.statements = [{ id: "lax1.C.s", signature: "s : True" }];
    old.output!.proofs = [{
      id: "lax1Proofs.p", path: "proofs/P.lean", conclusion: "lax1.C.s",
      assumptions: [], description: "d",
    }];
    const bare: SiteSubmission = {
      record: { specVersion: "1", id: "lax-4", state: "registered", createdAt: "2026-01-01T00:00:00Z" },
    };
    const root = tmpDir("lax-site-versions-edges-");
    await generateSite([
      old,
      make("lax-2", "registered", "New Result", "lax-1"),
      bare,
      make("lax-5", "registered", "Bare Successor", "lax-4"),
    ], root);

    const proofPage = fs.readFileSync(path.join(root, "lax-1", "lax1Proofs.p.html"), "utf8");
    expect(proofPage).toContain('class="version-notice version-notice-superseded"');
    expect(proofPage).toContain('href="../lax-2/index.html?version=lax-2"');
    expect(proofPage).toContain("assets/version-history.js");

    const barePage = fs.readFileSync(path.join(root, "lax-4", "index.html"), "utf8");
    expect(barePage).toContain("No content uploaded yet");
    expect(barePage).toContain('class="version-notice version-notice-superseded"');
    expect(barePage).toContain('href="../lax-5/index.html?version=lax-5"');
  });

  it("keeps superseded work out of the library, sidebar, and discovery card", async () => {
    const root = tmpDir("lax-site-versions-index-");
    await generateSite(archive(), root);
    const index = fs.readFileSync(path.join(root, "index.html"), "utf8");
    expect(index).not.toContain('data-entry-group="superseded"');
    expect(index).not.toContain('data-state="superseded"');
    expect(index).not.toContain('data-search-title="lax-1 old result"');
    expect(index).not.toContain('href="lax-1/index.html"');
    expect(index).not.toContain('data-search-title="lax-2 middle result"');
    expect(index).toContain("2 submissions · 2 concepts");
    expect(index).toContain('data-random-submission-candidate');
    expect(index).not.toContain('href="lax-1/index.html" data-random-submission-candidate');
  });
});

describe("multi-statement concepts", () => {
  /** One claim-concept declaring three statements: the first is proven
   * outright, the third from the first and the second of the same concept,
   * and the second stays open. Plus a definition-concept, so the concept map
   * keeps both fills. */
  const multiStatement = (): SiteSubmission[] => [{
    record: {
      specVersion: "1", id: "Lax5", state: "registered", createdAt: "2026-01-01T00:00:00Z",
      registeredAt: "2026-01-02T00:00:00Z",
      source: { repository: "https://github.com/example/menger", commit: "b".repeat(40), folder: "." },
    },
    output: {
      specVersion: "1", id: "Lax5",
      manifest: {
        specVersion: "1", id: "Lax5", leanVersion: "v4.30.0", mathlibVersion: "abc",
        title: "Menger", authors: [], bibEntries: [],
      },
      abstract: "", requiredByConcepts: [], requiredByProofs: [],
      concepts: [
        {
          id: "Lax5.Menger", path: "concepts/Lax5/Menger.lean", title: "Menger's theorem",
          type: "theorem", description: "Three faces of one theorem.",
          imports: [], mathlibImports: [],
          sourceText: [
            "namespace Lax5.Menger",
            "axiom vertexVersion : True",
            "axiom edgeVersion : True",
            "axiom globalVersion : True",
            "end Lax5.Menger",
          ].join("\n"),
          statements: [
            { id: "Lax5.Menger.vertexVersion", signature: "vertexVersion : True", startLine: 2, endLine: 2 },
            { id: "Lax5.Menger.edgeVersion", signature: "edgeVersion : True", startLine: 3, endLine: 3 },
            { id: "Lax5.Menger.globalVersion", signature: "globalVersion : True", startLine: 4, endLine: 4 },
          ],
        },
        {
          id: "Lax5.Graph", path: "concepts/Lax5/Graph.lean", title: "Graphs", type: "definition",
          description: "", imports: [], mathlibImports: [], sourceText: "", statements: [],
        },
      ],
      proofs: [
        {
          id: "Lax5Proofs.vertex", path: "proofs/Lax5Proofs/Vertex.lean",
          conclusion: "Lax5.Menger.vertexVersion", assumptions: [], description: "Direct.",
        },
        {
          id: "Lax5Proofs.global", path: "proofs/Lax5Proofs/Global.lean",
          conclusion: "Lax5.Menger.globalVersion",
          assumptions: ["Lax5.Menger.vertexVersion", "Lax5.Menger.edgeVersion"],
          description: "From both versions.",
        },
      ],
    },
  }];

  it("numbers English ordinals correctly", () => {
    const cases: [number, string][] = [
      [1, "1st"], [2, "2nd"], [3, "3rd"], [4, "4th"], [11, "11th"], [12, "12th"],
      [13, "13th"], [21, "21st"], [22, "22nd"], [23, "23rd"], [101, "101st"], [111, "111th"],
    ];
    for (const [value, expected] of cases) expect(ordinal(value)).toBe(expected);
  });

  it("names a statement by its anonymous position inside its concept", () => {
    const model = new SiteModel(multiStatement());
    expect(statementOrdinal(model, "Lax5.Menger.vertexVersion"))
      .toEqual({ index: 1, count: 3, label: "1st statement" });
    expect(statementOrdinal(model, "Lax5.Menger.globalVersion"))
      .toEqual({ index: 3, count: 3, label: "3rd statement" });
    // a single-statement concept *is* its claim and takes no ordinal
    expect(statementOrdinal(new SiteModel(submissions()), "Lax2.C.truth")).toBeUndefined();
  });

  it("gives every statement its own evidence block and proof rail", async () => {
    const root = tmpDir("lax-site-multi-concept-");
    await generateSite(multiStatement(), root);
    const html = fs.readFileSync(path.join(root, "Lax5", "Lax5.Menger.html"), "utf8");

    expect(html).toContain("This concept declares 3 statements. Each proof establishes one of them relative to its assumptions.");
    expect((html.match(/class="evidence-statement"/g) ?? []).length).toBe(3);
    expect(html).toContain('<h4><a href="#s-Lax5.Menger.vertexVersion">1st statement</a> <code>vertexVersion</code>');
    expect(html).toContain('<h4><a href="#s-Lax5.Menger.edgeVersion">2nd statement</a> <code>edgeVersion</code>');
    expect(html).toContain('<h4><a href="#s-Lax5.Menger.globalVersion">3rd statement</a> <code>globalVersion</code>');
    // the open second statement says so, and only it
    expect((html.match(/this statement is open/g) ?? []).length).toBe(1);
    const openBlock = html.slice(html.indexOf("#s-Lax5.Menger.edgeVersion"), html.indexOf("#s-Lax5.Menger.globalVersion"));
    expect(openBlock).toContain("this statement is open");
    // one rail per statement that has proofs, each on its own declaration row
    const rails = [...html.matchAll(/<span class="source-proof-rail" data-source-line="(L\d+)"/g)]
      .map((match) => match[1]);
    expect(rails).toEqual(["L2", "L4"]);
    // the concept as a whole is open while one statement is unproven
    expect(html).toContain('<span class="status-pill pill-partial"');
  });

  it("shows which statement a proof concludes and never which one it assumes", async () => {
    const root = tmpDir("lax-site-multi-proof-");
    await generateSite(multiStatement(), root);
    const html = fs.readFileSync(path.join(root, "Lax5", "Lax5Proofs.global.html"), "utf8");

    expect(html).toContain("<h1 class=\"concept-title\">Proof of <span class=\"proof-concept-title\">`Menger's theorem`</span> <span class=\"claim-ordinal\">(3rd statement)</span></h1>");
    const conclusion = html.slice(html.indexOf('class="judgment-conclusion"'));
    expect(conclusion).toContain('href="../Lax5/Lax5.Menger.html#s-Lax5.Menger.globalVersion" title="Lax5.Menger.globalVersion"');
    expect(conclusion).toContain('<span class="claim-ordinal">(3rd statement)</span>');
    // both assumed statements belong to one concept: one entry, no ordinal,
    // and a title that names the concept rather than the statement used
    const assumptions = html.slice(html.indexOf('class="judgment-assumptions"'), html.indexOf('class="judgment-arrow"'));
    expect((assumptions.match(/class="claim-entry"/g) ?? []).length).toBe(1);
    expect(assumptions).not.toContain("claim-ordinal");
    expect(assumptions).toContain('href="../Lax5/Lax5.Menger.html" title="Lax5.Menger"');
    expect(assumptions).not.toContain("#s-");
    // the aggregate claim is still open, so the badge says so
    expect(assumptions).toContain("thm×");
    expect(html).toContain("conditional — 1 open assumption");
  });

  it("carries statement positions and every sibling into the graph data", async () => {
    const root = tmpDir("lax-site-multi-graph-");
    await generateSite(multiStatement(), root);
    const html = fs.readFileSync(path.join(root, "Lax5", "index.html"), "utf8");
    const data = JSON.parse(/<script type="application\/json" id="graph-data">(.*?)<\/script>/s.exec(html)![1]!);

    expect(data.proofs.statements.map((s: { id: string }) => s.id)).toEqual([
      "Lax5.Menger.edgeVersion", "Lax5.Menger.globalVersion", "Lax5.Menger.vertexVersion",
    ]);
    for (const statement of data.proofs.statements)
      expect(statement).toMatchObject({ concept: "Lax5.Menger", count: 3, ext: false });
    expect(data.proofs.statements.map((s: { index: number }) => s.index)).toEqual([2, 3, 1]);
    // globalVersion rests on the still-open edgeVersion, so only the first
    // statement is proven
    expect(data.proofs.statements.map((s: { proven: boolean }) => s.proven)).toEqual([false, false, true]);
    // the concept map reports the claim as open while one statement is not proven
    expect(data.concepts.nodes.map((n: { id: string; status: string }) => [n.id, n.status]))
      .toEqual([["Lax5.Graph", "none"], ["Lax5.Menger", "open"]]);
    // the legend gains the dock swatch exactly here
    expect(html).toContain('<i class="legend-dock" aria-hidden="true">1</i>Statement 1, 2, … of a claim with several statements');
  });
});
