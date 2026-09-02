import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { SITE_MIME, siteAssetPath } from "../src/sitegen/assets.js";
import { generateSite, type SiteSubmission } from "../src/sitegen/generate.js";
import { countsPill, typeBadge, typeBadgeText } from "../src/sitegen/html.js";
import { compareIds, SiteModel } from "../src/sitegen/model.js";
import { MarkdownRenderer } from "../src/sitegen/markdown.js";
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
  it("uses numeric archive ordering", () => {
    expect(["Lax10", "Lax2", "Lax1"].sort(compareIds)).toEqual(["Lax1", "Lax2", "Lax10"]);
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
    expect(concept).toMatch(/<h1 class="concept-title">The <em>small<\/em> <span class="katex"/);
    expect(concept).toMatch(/<h3>Case <span class="katex"/);
    expect(proof).toMatch(/<h3>Step <span class="katex"/);
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
    expect(css).toContain(".landing-demo-card:hover .landing-demo-inner");
    expect(css).toContain("transform: rotateY(180deg)");
    expect(css).toContain("backface-visibility: hidden");
    expect(css).toContain("@media (hover: hover) and (pointer: fine)");
    expect(css).toContain("aspect-ratio: 1.42 / 1");
    expect(css).toContain(".landing-demo-concept .landing-demo-code-line-accent");
    expect(css).toContain(".landing-review-start[hidden]{ display: none; }");
    const unavailableRest = css.match(/\.landing-action-card\.unavailable\{([^}]*)\}/)?.[1] ?? "";
    expect(unavailableRest).not.toContain("background");
    expect(css).toMatch(/\.landing-action-card\.unavailable:hover,[\s\S]*?background: var\(--panel-bg\);/);
    expect(css).toContain("-webkit-line-clamp: 2");
    const landingScript = fs.readFileSync(path.join(one, "assets", "landing.js"), "utf8");
    const sidebarScript = fs.readFileSync(path.join(one, "assets", "sidebar.js"), "utf8");
    expect(landingScript).toContain("target.scrollIntoView({ behavior, block: 'start' })");
    expect(landingScript).toContain("url.searchParams.set('view', id)");
    expect(landingScript).toContain("window.addEventListener('popstate'");
    expect(landingScript).toContain("const initialView = urlView()");
    expect(landingScript).toContain("document.querySelector('[data-copy-prompt]')");
    expect(landingScript).not.toContain("data-open-paper");
    expect(landingScript).toContain("document.getElementById(`landing-panel-${id}`)");
    expect(landingScript).toContain("function setupProofFlip()");
    expect(landingScript).toContain("function setupReviewConcept()");
    expect(landingScript).toContain("Math.max(1, Number(option.dataset.reviewWeight) || 1)");
    expect(landingScript).not.toContain("Math.sqrt");
    expect(landingScript).not.toContain("sessionStorage");
    expect(landingScript).toContain("Math.random()");
    expect(landingScript).toContain("card.setAttribute('aria-pressed', String(flipped))");
    expect(landingScript).toContain("precisePointer.matches && event.detail !== 0");
    expect(landingScript).not.toContain("panel.hidden");
    expect(landingScript).not.toContain("aria-expanded");
    expect(sidebarScript).toContain("document.querySelectorAll('[data-tag-filter]')");
    expect(sidebarScript).toContain("url.searchParams.set('tag', tag)");
    expect(sidebarScript).toContain("updateTagStatus(visible)");
    expect(sidebarScript).toContain("function applySidebarFilters()");
    expect(sidebarScript).toContain("el.dataset.searchTitle !== undefined");
    expect(sidebarScript).toContain("function applySubmissionFilters()");
    expect(sidebarScript).toContain("filterList(list, search, type, 'entry-list-empty');");
    expect(sidebarScript).not.toContain("filterList(list, search, type, 'entry-list-empty', selectedTag)");
    expect(sidebarScript).toContain("function setupRandomSubmission()");
    expect(sidebarScript).toContain("Math.floor(Math.random() * candidates.length)");
    expect(sidebarScript).toContain("randomSubmission.hidden = Boolean(searchEl?.value.length)");
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
    expect(index).not.toContain('class="landing-about"');
    expect(index).not.toContain('<details class="landing-paper"');
    expect(index).toContain('class="landing-demo-card" type="button" data-proof-flip aria-pressed="false"');
    expect(index).toContain('<strong>Concept file</strong>');
    expect(index).toContain('<strong>Proof file</strong>');
    expect(index).toContain('<strong>Meaning</strong><small>read by people</small>');
    expect(index).toContain('<strong>Evidence</strong><small>checked by Lean</small>');
    expect(index).toContain('class="landing-demo-file-note">excerpt</span>');
    expect(index).toContain('class="landing-demo-continuation" aria-hidden="true"');
    expect(index).toContain('class="landing-demo-code-line landing-demo-code-line-accent" data-line="14"');
    expect(index).toContain('class="landing-demo-code-line" data-line="417"');
    expect(index).toContain('class="landing-demo-code-line" data-line="429"');
    expect(index).not.toContain("landing-demo-file-icon");
    expect(index).not.toContain("landing-demo-side");
    expect(index).not.toContain("landing-demo-trust-index");
    expect(index).not.toContain("landing-demo-instruction");
    expect(index).not.toContain("See the concept");
    expect((index.match(/See the proof/g) ?? []).length).toBe(1);
    expect(index).toContain('concepts/ErdosHajnal/C5.lean');
    expect(index).toContain('proofs/ErdosHajnalProofs/C5.lean');
    expect(index).toContain('cycleGraph');
    expect(index).toContain('polynomial_homogeneous_set_for_five_hole');
    expect(index).toMatch(/class="landing-demo-code-line" data-line="1"><span style="color:/);
    expect(index).not.toMatch(/landing-demo-code-line[^]*?\bsorry\b/);
    expect(index).toContain("Formalized mathematics that can be read, checked, and built upon.");
    expect(index).toMatch(/Think of\s+it as an arXiv for formalization/);
    expect(index).toContain('class="landing-hero-button primary" type="button" data-landing-action="read"');
    expect(index).toContain('class="landing-hero-button secondary" href="assets/lax-white-paper.pdf" download="lax-white-paper.pdf"');
    expect(index.indexOf("landing-lede")).toBeLessThan(index.indexOf("landing-demo-card"));
    expect(index.indexOf("landing-demo-card")).toBeLessThan(index.indexOf("landing-demo-summary"));
    expect(index.indexOf("landing-demo-summary")).toBeLessThan(index.indexOf("landing-actions"));
    expect(index).toContain('<h2 id="landing-actions-heading">What you can do here</h2>');
    expect(index).toContain('data-landing-action="read" aria-controls="landing-panel-read"');
    expect(index).toContain('data-landing-action="submit" aria-controls="landing-panel-submit"');
    expect(index).toContain('data-landing-action="cite" aria-controls="landing-panel-cite"');
    expect(index).toContain('data-landing-action="review" aria-controls="landing-panel-review"');
    for (const id of ["read", "review", "submit", "cite"]) {
      expect(index).toContain(`id="landing-action-${id}"`);
      expect(index).toContain(`data-landing-view="${id}"`);
    }
    expect(index).not.toContain('class="landing-action-card unavailable"');
    expect(index).not.toContain("Coming soon");
    expect(index).toContain('<section class="landing-action-panel submissions-library" id="landing-panel-read" aria-labelledby="landing-action-read">');
    expect(index).toContain("<h3>Submissions</h3>");
    expect(index).toContain("Creating your own submission");
    expect(index).toContain('<div class="landing-prompt-box">');
    expect(index).toContain('<pre id="landing-submission-prompt"><code>');
    expect(index).toContain('data-copy-prompt aria-controls="landing-submission-prompt" aria-label="Copy prompt to clipboard"');
    expect(index).toContain('<output class="prompt-copy-status" aria-live="polite"></output>');
    expect(index).toContain('id="landing-panel-submit" aria-labelledby="landing-action-submit">');
    expect(index).toContain('id="landing-panel-cite" aria-labelledby="landing-action-cite">');
    expect(index).toContain('id="landing-panel-review" aria-labelledby="landing-action-review">');
    expect(index).toContain("<h3>Review a concept</h3>");
    // An import from another concept in the same submission is not enough to
    // make a concept eligible for the archive-wide review suggestion.
    expect(index).not.toContain('data-review-concept="Lax2.C"');
    expect(index).toContain("Review a concept or submission, endorse correct mathematics, or flag possible flaws.");
    const reviewPanelStart = index.indexOf('id="landing-panel-review"');
    const reviewPanelEnd = index.indexOf("</section>", reviewPanelStart);
    const reviewPanel = index.slice(reviewPanelStart, reviewPanelEnd);
    expect(reviewPanel).not.toContain("open-proof-obligations.html");
    expect(index).toContain('<section class="landing-action-panel landing-proof-obligations-panel" id="landing-proof-obligations" aria-labelledby="landing-proof-obligations-heading">');
    expect(index).toContain('<h3 id="landing-proof-obligations-heading">Open proof obligations</h3>');
    expect(reviewPanelEnd).toBeLessThan(index.indexOf('id="landing-proof-obligations"'));
    expect(index).toContain('class="landing-open-problems-link" href="open-proof-obligations.html"');
    expect(index).not.toMatch(/id="landing-panel-(?:read|submit|cite)"[^>]* hidden/);
    expect(index.indexOf('id="landing-panel-submit"')).toBeLessThan(index.indexOf('id="landing-panel-read"'));
    expect(index.indexOf('id="landing-panel-read"')).toBeLessThan(index.indexOf('id="landing-panel-cite"'));
    expect(index).toContain('Go to section <b>↓</b>');
    expect(index).toContain("Every submission page ends with a <strong>Citation</strong> section");
    expect(index).toContain('class="landing-cite-example"');
    expect(index).toContain('href="Lax2/index.html#citation"');
    expect(index).toContain('class="landing-cite-example-action">View citation');
    expect(index).toContain("contributing.html");
    expect(index).toMatch(/<script src="assets\/landing\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(index).toMatch(/<script src="assets\/sidebar\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(index).toMatch(/<script src="assets\/account\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(index).toContain('data-account-login');
    expect(index).toContain('data-account-settings');
    expect(index).toContain('<nav class="header-actions" aria-label="Account">');
    expect(index).not.toContain('class="header-submit"');
    expect(index).toContain('<span>Sign in with ORCID</span>');
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

  it("weights review concepts by distinct external submissions and reports both reuse counts", async () => {
    const archive = graphSubmissions();
    const middle = archive[1]!.output!.concepts[0]!;
    const [top, auxiliary] = archive[2]!.output!.concepts;
    top!.imports.push("Lax1.Base");
    auxiliary!.imports.push("Lax1.Base");
    // Same-submission reuse still contributes to the concept count, but a
    // candidate must also be reused by at least one other submission.
    archive[0]!.output!.concepts.push({
      id: "Lax1.Internal", path: "concepts/Lax1/Internal.lean", title: "Internal",
      type: "definition", description: "", imports: ["Lax1.Base"],
      mathlibImports: [], sourceText: "", statements: [],
    }, {
      id: "Lax1.LocalOnly", path: "concepts/Lax1/LocalOnly.lean", title: "Local only",
      type: "definition", description: "", imports: [],
      mathlibImports: [], sourceText: "", statements: [],
    });
    middle.imports.push("Lax1.LocalOnly");

    const root = tmpDir("lax-site-review-weight-");
    await generateSite(archive, root);
    const index = fs.readFileSync(path.join(root, "index.html"), "utf8");

    // Lax1.Base has four importing concepts across two external submissions:
    // 2 * 10 + 4 = 24. Its same-submission importer is included in the concept
    // count, while Lax1.LocalOnly remains eligible because Lax3 imports it.
    expect(index).toContain('data-review-concept="Lax1.Base" data-review-weight="24"');
    expect(index).toContain("Used by 2 other submissions and 4 other concepts");
    expect(index).toContain('data-review-concept="Lax3.Middle" data-review-weight="11" hidden');
    expect(index).toContain("Used by 1 other submission and 1 other concept");
    expect(index).toContain("This concept is reused elsewhere in the archive. Review its mathematical correctness, endorse it if correct, or flag a flaw.");
    expect(index).toContain('>Review now <b aria-hidden="true">→</b></a>');
    expect(index).toContain('data-review-concept="Lax1.LocalOnly"');
    expect(index).not.toContain('data-review-concept="Lax1.Internal"');
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
    await generateSite([...submissions(), ...graphSubmissions()], root);
    const html = fs.readFileSync(path.join(root, "open-proof-obligations.html"), "utf8");

    expect(html).toContain("2 proof obligations · 2 open statements · 1 submission");
    expect(html).toContain('placeholder="Search proof obligations"');
    expect(html).toContain('id="open-problems-list"');
    expect(html).toContain('data-type="theorem"');
    expect(html).toContain('href="Lax4/Lax4.Top.html"');
    expect(html).toContain('href="Lax4/Lax4.Aux.html"');
    expect(html).toContain("Lax4.Top.a");
    expect(html).toContain("Lax4.Aux.b");
    expect(html).not.toContain('href="Lax2/Lax2.C.html"');
    expect(html).not.toContain('href="Lax1/Lax1.Base.html"');
  });

  it("uses Lax17 as the landing citation example when it is available", async () => {
    const archive = submissions();
    const lax17 = structuredClone(archive[0]!);
    lax17.record.id = "lax-17";
    lax17.record.state = "draft";
    lax17.record.registeredAt = undefined;
    lax17.output!.id = "lax-17";
    lax17.output!.manifest.id = "lax-17";
    lax17.output!.manifest.title = "A Polynomial Bound for the Grid-Minor Theorem";
    lax17.output!.abstract = "";
    lax17.output!.concepts = [];
    lax17.output!.proofs = [];

    const root = tmpDir("lax-site-cite-example-");
    await generateSite([...archive, lax17], root);
    const index = fs.readFileSync(path.join(root, "index.html"), "utf8");
    expect(index).toContain('href="lax-17/index.html#citation"');
    expect(index).toContain("A Polynomial Bound for the Grid-Minor Theorem");
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
    // the concept box explains its own badges, real components as samples
    expect(html).toContain('class="badge-legend"');
    expect(html.indexOf('class="concept-list"')).toBeLessThan(html.indexOf('class="badge-legend"'));
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
    expect(html.indexOf('class="proof-list"')).toBeLessThan(html.indexOf('id="proof-network"'));
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
    expect(html).toContain('data-reaction="endorse"');
    expect(html).toContain('data-reaction="flag"');
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
    expect(html).toContain("your ORCID profile must share a public name.");
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
    // home concept (one-statement rule) with the raw id kept for tooltips
    expect(data.concepts.nodes.map((n: { id: string; status: string }) => [n.id, n.status]))
      .toEqual([["Lax2.C", "proven"], ["Lax2.D", "none"]]);
    expect(data.proofs.statements[0]).toMatchObject({
      id: "Lax2.C.truth", label: "Lax2.C", owner: "Lax2", proven: true, ext: false,
    });
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
    expect(html).toContain('<span class="proof-flow">assumptions <i class="legend-arrow" aria-hidden="true">→</i><i class="legend-proof-chip" aria-hidden="true">⊢</i><i class="legend-arrow" aria-hidden="true">→</i> conclusion</span>');
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
    const badges = legend(grounded, "Concept badge legend", "div");
    expect(badges).toContain("proven claim");
    expect(badges).not.toContain("open claim");
    expect(badges).toContain("definition");
    expect(badges).not.toContain("letters abbreviate");
    inOrder(badges, ["proven claim", "definition"]);

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
    inOrder(groundedProofs, ["proof-flow", "fill-proven", "stroke-own", "Proof — click to open"]);

    // Lax4's claims are open, its concept ancestry contains definitions from
    // other submissions, and its two proofs form a cycle.
    const cyclic = fs.readFileSync(path.join(root, "Lax4", "index.html"), "utf8");
    const cyclicBadges = legend(cyclic, "Concept badge legend", "div");
    expect(cyclicBadges).not.toContain("proven claim");
    expect(cyclicBadges).toContain("open claim");
    expect(cyclicBadges).not.toContain("definition");

    const cyclicConcepts = legend(cyclic, "Concept map legend", "figcaption");
    expect(cyclicConcepts).not.toContain("fill-proven");
    inOrder(cyclicConcepts, ["fill-open", "fill-none", "stroke-own", "stroke-ext", "legend-arrow"]);

    const cyclicProofs = legend(cyclic, "Proof network legend", "figcaption");
    expect(cyclicProofs).not.toContain("fill-proven");
    expect(cyclicProofs).not.toContain("stroke-ext");
    inOrder(cyclicProofs, ["proof-flow", "fill-open", "stroke-own", "Proof — click to open", "legend-cycle"]);
  });

  it("emits expandable concept closures and proof readiness metadata for deterministic DAGs", async () => {
    const root = tmpDir("lax-site-graphs-");
    await generateSite([...submissions(), ...graphSubmissions()], root);
    const html = fs.readFileSync(path.join(root, "Lax4", "index.html"), "utf8");
    // ancestors are on by default, descendants off — both closures run over
    // the whole archive, not just this submission
    expect(html).toContain('id="concept-expand"');
    expect(html).toContain("Hide ancestors");
    expect(html).toContain('data-graph="concepts" data-ancestry="true"');
    expect(html).toContain('id="concept-descend"');
    expect(html).toContain("Show descendants");
    expect(html).not.toContain('aria-controls="concept-dag" aria-pressed="false">Hide');
    // figure titles sit in the flow above the boxes, not inside the chrome
    expect(html).toContain('<h4 class="figure-title">Concept map</h4>');
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
    expect(script).toContain("proof.assumptions.length === 1");
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

  it("maps each submission's dependants and dependencies across the whole archive", async () => {
    const root = tmpDir("lax-site-submap-");
    await generateSite([...submissions(), ...graphSubmissions()], root);
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
    expect(top.data.nodes.map((n: { id: string; dir: string }) => [n.id, n.dir]))
      .toEqual([["Lax1", "up"], ["Lax3", "up"], ["Lax4", "core"]]);
    expect(top.data.edges).toEqual([{ from: "Lax1", to: "Lax3" }, { from: "Lax3", to: "Lax4" }]);
    expect(top.data.nodes[0]).toMatchObject({ href: "../Lax1/index.html", title: "Lax1", state: "registered", concepts: 1, proofs: 0, ext: true });

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
    expect([...model.submissionUses.get("Lax2")!]).toEqual(["Lax1"]);
    expect(model.submissionDownstream("Lax1")).toEqual(["Lax2", "Lax3", "Lax4"]);
    // "mathlib" is not a submission and never becomes a node
    expect(model.submissionById.has("mathlib")).toBe(false);
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
    expect(html).toContain("<h3>Builds on</h3>");
    expect(html).toContain("<h3>Used by</h3>");
    expect(html).toContain("<h3>From Mathlib</h3>");
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
    expect(html.indexOf('class="concept-id"')).toBeLessThan(html.indexOf('class="concept-title"'));
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
    // the proofs group follows the concepts, ⊢-chipped, prefix-pruned,
    // filterable as its own type
    expect(sidebar.indexOf(">Concepts</li>")).toBeLessThan(sidebar.indexOf(">Proofs</li>"));
    expect(sidebar).toMatch(/data-type="proof"[^]*?proof-badge[^]*?>truth</);
    expect(sidebar).toContain('<option value="proof">proof</option>');
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

  it("fails fast on statements without a home and on multi-statement concepts", async () => {
    const broken = submissions();
    broken[0]!.output!.proofs[0]!.assumptions = ["Nobody.here"];
    await expect(generateSite(broken, tmpDir("lax-site-nohome-"))).rejects.toThrow(
      "statement Nobody.here has no home concept",
    );
    const multi = submissions();
    multi[0]!.output!.concepts[0]!.statements.push({ id: "Lax2.C.more", signature: "more : True" });
    await expect(generateSite(multi, tmpDir("lax-site-multi-"))).rejects.toThrow("one-statement rule");
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
    expect(model.latestVersion("lax-1")).toBe("lax-3");
    expect(model.latestVersion("lax-2")).toBe("lax-3");
    expect(model.versionChain("lax-1")).toEqual(["lax-1", "lax-2", "lax-3"]);
    expect(model.versionChain("lax-2")).toEqual(["lax-1", "lax-2", "lax-3"]);
    expect(model.versionChain("lax-3")).toEqual(["lax-1", "lax-2", "lax-3"]);
    expect(model.versionChain("lax-4")).toEqual(["lax-4"]);
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
    expect(oldPage).toContain("The current version is");
    expect(oldPage).toContain('href="../lax-3/index.html?version=lax-3"');
    expect(oldPage).toContain("Current Result");
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
    expect(oldPage.indexOf('class="paper-head"')).toBeLessThan(oldPage.indexOf('class="version-notice'));
    expect(oldPage.indexOf('class="version-notice')).toBeLessThan(oldPage.indexOf('class="paper-abstract"'));

    const oldConcept = fs.readFileSync(path.join(root, "lax-1", "lax1.C.html"), "utf8");
    expect(oldConcept).toContain('class="version-notice version-notice-superseded"');
    expect(oldConcept).toContain('href="../lax-3/index.html?version=lax-3"');
    expect(oldConcept).toContain("assets/version-history.js");

    const middlePage = fs.readFileSync(path.join(root, "lax-2", "index.html"), "utf8");
    expect(middlePage).toContain('class="version-notice version-notice-superseded"');
    expect(middlePage).toContain('href="../lax-3/index.html?version=lax-3"');
    expect(middlePage).toContain('class="version-item version-selected"');

    const currentPage = fs.readFileSync(path.join(root, "lax-3", "index.html"), "utf8");
    expect(currentPage).not.toContain('class="version-notice');
    expect(currentPage).toContain('class="paper-version-button" type="button"');
    expect(currentPage).toContain(">3 versions</button>");
    expect(currentPage).toContain('data-version-dialog');
    const currentMeta = currentPage.slice(currentPage.indexOf('<p class="paper-meta">'), currentPage.indexOf("</p>", currentPage.indexOf('<p class="paper-meta">')));
    expect(currentMeta.indexOf("paper-version-button")).toBeGreaterThan(currentMeta.indexOf("mathlib"));
    expect(currentPage).toContain('href="../lax-1/index.html?version=lax-1"');
    expect(currentPage).toContain('href="../lax-2/index.html?version=lax-2"');
    expect(currentPage).toContain("version-mark-latest");
    expect(currentPage).toContain("version-mark-viewing");
    expect(currentPage).not.toContain("note = {superseded");

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
