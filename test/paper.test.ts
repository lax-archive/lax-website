import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { loadSubmissions, submissionsMissingPapers } from "../src/database.js";
import { generateSite, type SiteSubmission } from "../src/sitegen/generate.js";
import { paperCachePath } from "../src/papers.js";
import { createRequire } from "node:module";
import { VENDORED_PDFJS } from "../scripts/vendor-pdfjs.mjs";
import { tmpDir } from "./helpers.js";

const pdf = Buffer.from("%PDF-1.7\n% a stand-in for the compiled paper\n");
const digest = createHash("sha256").update(pdf).digest("hex");
const source = { repository: "https://github.com/example/spike.git", commit: "a".repeat(40), folder: "." };

/** lax-7 carries a paper marking its own concept and proof, a concept of
 * lax-3, and lax-3 itself; lax-3 has no paper. */
function archive(): SiteSubmission[] {
  return [{
    record: { specVersion: "1", id: "lax-3", state: "registered", createdAt: "2026-08-01T00:00:00Z", source },
    output: {
      specVersion: "1", id: "lax-3",
      manifest: { specVersion: "1", id: "lax-3", leanVersion: "v4.30.0", mathlibVersion: "c".repeat(40), title: "Bags and separations", authors: [], bibEntries: [] },
      abstract: "The base.", requiredByConcepts: [], requiredByProofs: [],
      concepts: [{ id: "Lax3.Bags", path: "concepts/Lax3/Bags.lean", title: "Bags", type: "definition", description: "The bags.", imports: [], mathlibImports: [], sourceText: "", statements: [] }],
      proofs: [],
    },
  }, {
    record: { specVersion: "1", id: "lax-7", state: "registered", createdAt: "2026-09-01T00:00:00Z", source },
    output: {
      specVersion: "1", id: "lax-7",
      manifest: { specVersion: "1", id: "lax-7", leanVersion: "v4.30.0", mathlibVersion: "c".repeat(40), title: "A Spike Paper", authors: [], bibEntries: [] },
      abstract: "With a paper.", requiredByConcepts: ["Lax3"], requiredByProofs: [],
      concepts: [
        { id: "Lax7.Treewidth", path: "concepts/Lax7/Treewidth.lean", title: "Treewidth is $monotone$", type: "theorem", description: "Does not grow.", imports: ["Lax3.Bags"], mathlibImports: [], sourceText: TREEWIDTH_SOURCE, statements: [{ id: "Lax7.Treewidth.mono", signature: "mono : True", startLine: 10, endLine: 10 }] },
      ],
      proofs: [{ id: "Lax7Proofs.mono", path: "proofs/Lax7Proofs/Mono.lean", conclusion: "Lax7.Treewidth.mono", assumptions: [], description: "Direct." }],
      paper: {
        folder: "paper", main: "main.tex", engine: "pdflatex",
        pdf: { digest, bytes: pdf.length, pages: 2, registryBlob: `ghcr.io/lax-archive/lax-captures@sha256:${digest}` },
        pageSizes: [[595.28, 841.89], [595.28, 841.89]],
        marks: [
          { id: "Lax7.Treewidth", kind: "concept", begin: { page: 1, x: 72, y: 700, mode: "v" }, end: { page: 1, x: 72, y: 600, mode: "v" } },
          { id: "Lax7Proofs.mono", kind: "proof", begin: { page: 1, x: 300, y: 500, mode: "h" }, end: { page: 2, x: 100, y: 700, mode: "h" } },
          { id: "Lax3.Bags", kind: "concept", begin: { page: 2, x: 72, y: 650, mode: "h" }, end: { page: 2, x: 200, y: 650, mode: "h" } },
          { id: "lax-3", kind: "submission", begin: { page: 2, x: 72, y: 400, mode: "v" }, end: { page: 2, x: 72, y: 300, mode: "v" } },
        ],
      },
    },
  }];
}

const TREEWIDTH_SOURCE = `import Lax3.Bags

/-!
---
title: Treewidth
---
Does not grow.
-/

/-- The declaration's own docstring stays. -/
theorem Lax7.Treewidth.mono : True := trivial
`;

function withPdf(submissions: SiteSubmission[]): SiteSubmission[] {
  const file = path.join(tmpDir("lax-paper-cache-"), `${digest}.pdf`);
  fs.writeFileSync(file, pdf);
  return submissions.map((s) => s.output?.paper ? { ...s, paperFile: file } : s);
}

describe("paper pages", () => {
  it("vendors exactly the pinned pdfjs-dist build", () => {
    const require = createRequire(import.meta.url);
    for (const [name, specifier] of Object.entries(VENDORED_PDFJS as Record<string, string>)) {
      const vendored = fs.readFileSync(path.join("assets", "site", "pdfjs", name));
      expect(vendored.equals(fs.readFileSync(require.resolve(specifier))), `${name} drifted from ${specifier}; run npm run pdfjs:vendor`).toBe(true);
    }
    expect(fs.readFileSync(path.join("assets", "site", "pdfjs", "VERSION.txt"), "utf8").trim())
      .toBe((require("pdfjs-dist/package.json") as { version: string }).version);
  });

  it("emits the paper page with the PDF, pre-rendered cards, and the viewer under its own CSP", async () => {
    const root = tmpDir("lax-site-paper-");
    await generateSite(withPdf(archive()), root);
    expect(fs.readFileSync(path.join(root, "lax-7", "paper.pdf"))).toEqual(pdf);
    expect(fs.existsSync(path.join(root, "lax-3", "paper.html"))).toBe(false);
    for (const asset of ["pdfjs/pdf.min.mjs", "pdfjs/pdf.worker.min.mjs", "pdfjs/LICENSE.txt", "manuscript.js", "manuscript-place.js"])
      expect(fs.existsSync(path.join(root, "assets", asset)), asset).toBe(true);
    const html = fs.readFileSync(path.join(root, "lax-7", "paper.html"), "utf8");
    expect(html).toContain("worker-src 'self'");
    expect(html).toContain("connect-src 'self' https://comments.laxarchive.org");
    expect(html).toContain('<div id="detail" class="detail-manuscript">');
    expect(html).toMatch(/<div class="manuscript" data-pdf="paper\.pdf" data-pdfjs="\.\.\/assets\/pdfjs\/pdf\.min\.mjs\?v=[0-9a-f]{12}" data-pdfjs-worker="\.\.\/assets\/pdfjs\/pdf\.worker\.min\.mjs\?v=[0-9a-f]{12}">/);
    expect(html).toMatch(/<script src="\.\.\/assets\/manuscript-place\.js\?v=[0-9a-f]{12}"><\/script>\n<script src="\.\.\/assets\/manuscript\.js\?v=[0-9a-f]{12}"><\/script>/);
    expect(html).toContain("2 pages · 4 marked passages · pdflatex · <a href=\"paper.pdf\">download PDF</a>");
    // one page box per page, sized before any rendering
    expect(html.match(/<div class="manuscript-page" data-page="\d+" style="aspect-ratio: 595\.28 \/ 841\.89"><\/div>/g)).toHaveLength(2);
    // cards in mark order, each in the vocabulary of the page it links to
    const cardOrder = [...html.matchAll(/<li class="manuscript-card ([^"]*)" id="m(\d+)"/g)].map((m) => [m[2], m[1]]);
    expect(cardOrder).toEqual([["1", "kind-concept line-proven"], ["2", "kind-proof line-proven"], ["3", "kind-concept"], ["4", "kind-submission"]]);
    expect(html).toContain('<a href="../lax-7/Lax7.Treewidth.html"><code>Lax7.Treewidth</code></a>');
    expect(html).toContain('<p class="manuscript-card-title">Treewidth is <span class="katex">');
    expect(html).toContain('class="judgment"');
    expect(html).toContain('<a href="../lax-3/index.html"><span class="submission-meta-id">lax-3</span></a>');
    expect(html).toContain("Bags and separations");
    expect(html).toContain('<span class="manuscript-card-page">pp. 1–2</span>');
    expect(html).toContain('aria-controls="m2-body"');
    // no list of marks above the columns: the cards beside the passages are the index
    expect(html).not.toContain("manuscript-index");
    // the inert payload the viewer reads
    const data = JSON.parse(/<script type="application\/json" id="manuscript-data">(.*?)<\/script>/.exec(html)![1]!);
    expect(data.pageSizes).toHaveLength(2);
    expect(data.marks[1]).toMatchObject({ n: 2, id: "Lax7Proofs.mono", kind: "proof", begin: { page: 1, x: 300, y: 500, mode: "h" } });
    // the sidebar leads back to the submission, and starts collapsed for the room
    expect(html).toContain('<a class="sidebar-back" href="../lax-7/index.html">');
    expect(html).toContain('<header class="site-header sidebar-hidden">');
    expect(html).toContain('<main id="content-shell" class="sidebar-hidden">');
    expect(fs.readFileSync(path.join(root, "lax-7", "Lax7.Treewidth.html"), "utf8")).toContain('<header class="site-header">');
    // the gutter bands' overlay
    expect(html).toContain('<svg class="manuscript-links" id="manuscript-links" aria-hidden="true"></svg>');
    // a concept card carries the Lean source, module docstring elided, without the concept page's row anchors
    const card = html.slice(html.indexOf('id="m1"'), html.indexOf('id="m2"'));
    expect(card).toContain('<div class="manuscript-card-source"><div class="inline-contract-wrap"><table class="inline-contract-table">');
    expect(card).toContain('<tr class="line-elided"><td class="line-num"></td><td class="line-code">… module docstring, 6 lines</td></tr>');
    expect(card).not.toContain("title: Treewidth");
    expect(card).toContain("own docstring stays.");
    expect(card).toMatch(/<tr class="statement-line line-proven"><td class="line-num">10<\/td>/);
    expect(card).not.toContain('id="L');
    expect(card).not.toContain('id="s-');
    expect(html).not.toContain('id="L1"');
  });

  it("links the paper from the submission, concept, and proof pages", async () => {
    const root = tmpDir("lax-site-paper-links-");
    await generateSite(withPdf(archive()), root);
    const submission = fs.readFileSync(path.join(root, "lax-7", "index.html"), "utf8");
    // one centered button after the abstract, the counts under it, no list of marks
    expect(submission).toContain('<section class="page-section paper-cta">\n<a class="source-button paper-cta-button" href="paper.html"><span>View annotated paper</span></a>\n<p class="paper-cta-facts">2 pages · 4 marked passages</p>\n</section>');
    expect(submission).not.toContain('manuscript-index');
    expect(submission).not.toContain('In the paper'); // its own mention is the button
    expect(submission.indexOf('class="paper-abstract"')).toBeLessThan(submission.indexOf('class="page-section paper-cta"'));
    expect(submission.indexOf('class="page-section paper-cta"')).toBeLessThan(submission.indexOf('<h3 class="section-title">Concepts</h3>'));
    const concept = fs.readFileSync(path.join(root, "lax-7", "Lax7.Treewidth.html"), "utf8");
    expect(concept).toContain('<h3>In the paper</h3>');
    expect(concept).toContain('<li><a href="../lax-7/paper.html#m1">page 1</a> of this submission\'s paper</li>');
    const proof = fs.readFileSync(path.join(root, "lax-7", "Lax7Proofs.mono.html"), "utf8");
    expect(proof).toContain('<li><a href="../lax-7/paper.html#m2">page 1</a> of this submission\'s paper</li>');
    // the foreign concept and the marked submission point at lax-7's paper
    const foreign = fs.readFileSync(path.join(root, "lax-3", "Lax3.Bags.html"), "utf8");
    expect(foreign).toContain('<li><a href="../lax-7/paper.html#m3">page 2</a> of the paper of <span class="submission-meta-id">lax-7</span>, A Spike Paper</li>');
    const marked = fs.readFileSync(path.join(root, "lax-3", "index.html"), "utf8");
    expect(marked).not.toContain('paper-cta');
    expect(marked).toContain('<a href="../lax-7/paper.html#m4">page 2</a> of the paper of');
  });

  it("renders the page without the viewer when the PDF is not attached (previews)", async () => {
    const root = tmpDir("lax-site-paper-preview-");
    await generateSite(archive(), root);
    expect(fs.existsSync(path.join(root, "lax-7", "paper.pdf"))).toBe(false);
    const html = fs.readFileSync(path.join(root, "lax-7", "paper.html"), "utf8");
    expect(html).not.toContain("worker-src");
    expect(html).not.toContain("manuscript.js");
    expect(html).not.toContain("data-pdf=");
    expect(html).toContain("not part of preview builds");
    expect(html).toContain('<ol class="manuscript-rail manuscript-rail-static">');
    expect(html).toContain('id="m4"');
    const submission = fs.readFileSync(path.join(root, "lax-7", "index.html"), "utf8");
    expect(submission).toContain("2 pages · 4 marked passages</p>");
    expect(submission).not.toContain('href="paper.pdf"');
  });

  it("attaches cached PDFs by digest when loading the database and names what is missing", async () => {
    const database = tmpDir("lax-database-paper-");
    const papers = tmpDir("lax-papers-cache-");
    for (const submission of archive()) {
      const dir = path.join(database, submission.record.id);
      fs.mkdirSync(dir);
      fs.writeFileSync(path.join(dir, "record.json"), JSON.stringify(submission.record));
      const { manifest, abstract, ...rest } = submission.output!;
      fs.writeFileSync(path.join(dir, "build-output.json"), JSON.stringify({ ...rest, inputs: { manifest, abstract } }));
    }
    const missing = loadSubmissions(database, { papersDir: papers });
    expect(submissionsMissingPapers(missing).map((s) => s.record.id)).toEqual(["lax-7"]);
    expect(submissionsMissingPapers(loadSubmissions(database)).map((s) => s.record.id)).toEqual(["lax-7"]);
    fs.writeFileSync(paperCachePath(papers, digest), pdf);
    const loaded = loadSubmissions(database, { papersDir: papers });
    expect(submissionsMissingPapers(loaded)).toEqual([]);
    expect(loaded.find((s) => s.record.id === "lax-7")?.paperFile).toBe(paperCachePath(papers, digest));
    expect(loaded.find((s) => s.record.id === "lax-7")?.output?.paper?.marks).toHaveLength(4);

    // a corrupt paper block fails the load with the record named
    const broken = JSON.parse(fs.readFileSync(path.join(database, "lax-7", "build-output.json"), "utf8"));
    broken.paper.marks[0].begin.page = 3;
    fs.writeFileSync(path.join(database, "lax-7", "build-output.json"), JSON.stringify(broken));
    expect(() => loadSubmissions(database)).toThrow(/lax-7.*paper mark 1 begin page is beyond the last page/);
    broken.paper.marks[0].begin.page = 1;
    broken.paper.pageSizes.pop();
    fs.writeFileSync(path.join(database, "lax-7", "build-output.json"), JSON.stringify(broken));
    expect(() => loadSubmissions(database)).toThrow("pageSizes must list one [width, height] pair per page");
  });
});
