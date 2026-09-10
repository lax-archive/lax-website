// The paper pages. `paper.html` is the paper: for a record whose reflow
// bundle passed the schema gate, the vendored ReflowTeX viewer paints the
// paper as reflowable SVG at the reader's width, the marks surface as
// `m<n>` anchors at exact stream positions (so every `paper.html#m<n>`
// link lands on the passage), and one pre-rendered card per mark joins its
// anchor (assets/manuscript-reflow.js); without a bundle it is the paper as
// printed instead. `paper-pdf.html` is always the paper as printed: the
// compiled PDF on the left, the cards on the right, placed by
// assets/manuscript.js. The two surfaces are two pages, each linking the
// other from a switch above the paper (the scripts carry `#m<n>` across).
// Without the PDF bytes — a preview build — the page still lists the cards
// and says where the paper went.
//
// The reflow page's footnotes join the same rail as sidenotes: the viewer
// emits each footnote's text as its own segment (an endnote) and its
// reference point as an `fn-ref-<k>` anchor, and the script lifts the
// segment into a footnote card it clones from the template shipped here,
// so the markup stays this generator's.

import { siteAssetVersion } from "../assets.js";
import { attr, code, esc, page, plural, proofBadge, typeBadge } from "../html.js";
import { inertJsonScript } from "../graphs.js";
import { highlightSource } from "../highlight.js";
import { compareIds, type SiteModel, type SiteSubmission } from "../model.js";
import type { PaperWebPage } from "../paper-web.js";
import type { PaperMark } from "../../types.js";
import {
  claimEntry,
  conceptShortName,
  draftBanner,
  environmentNotice,
  type PageContext,
  proofJudgment,
  proofShortName,
  submissionSidebar,
  versionHistoryPanel,
} from "./shared.js";

/** The name a mark's card leads with, shortened against the paper's own
 * submission like every other id on its pages, and where it links. */
function markTarget(model: SiteModel, mark: PaperMark, home: string, rootRel: string): { label: string; href?: string } {
  if (mark.kind === "concept") {
    const located = model.conceptHome.get(mark.id);
    return {
      label: located ? conceptShortName(located.output, located.concept) : mark.id,
      href: located ? `${rootRel}${located.output.id}/${located.concept.id}.html` : undefined,
    };
  }
  if (mark.kind === "proof") {
    const located = model.proofHome.get(mark.id);
    return {
      label: located ? proofShortName(located.output, located.proof, home) : mark.id,
      href: located ? `${rootRel}${located.output.id}/${located.proof.id}.html` : undefined,
    };
  }
  const submission = model.submissionById.get(mark.id);
  return { label: mark.id, href: submission ? `${rootRel}${mark.id}/index.html` : undefined };
}

/** The badge in front of a mark's name: the concept's type with its proven
 * mark, the proof chip, or the submission id styled as on the masthead. */
function markBadge(model: SiteModel, mark: PaperMark): string {
  if (mark.kind === "concept") {
    const located = model.conceptHome.get(mark.id);
    if (!located) return "";
    const statements = located.concept.statements;
    const provenCount = statements.filter((s) => model.network.proven.has(s.id)).length;
    return typeBadge(located.concept.type, statements.length ? provenCount === statements.length : undefined);
  }
  if (mark.kind === "proof") return proofBadge();
  return "";
}

/** `line-proven` / `line-open` as the Lean source uses them: what the card
 * stands for is a checked claim, an open one, or neither (definitions,
 * submissions). */
function markStatus(model: SiteModel, mark: PaperMark): string {
  if (mark.kind === "concept") {
    const located = model.conceptHome.get(mark.id);
    const statements = located?.concept.statements ?? [];
    if (!statements.length) return "";
    return statements.every((s) => model.network.proven.has(s.id)) ? " line-proven" : " line-open";
  }
  if (mark.kind === "proof") {
    const located = model.proofHome.get(mark.id);
    if (!located) return "";
    return located.proof.assumptions.every((id) => model.network.proven.has(id)) ? " line-proven" : " line-open";
  }
  return "";
}

function markName(model: SiteModel, mark: PaperMark, home: string, rootRel: string): string {
  const target = markTarget(model, mark, home, rootRel);
  const title = target.label === mark.id ? "" : ` title="${attr(mark.id)}"`;
  const name = mark.kind === "submission"
    ? `<span class="submission-meta-id">${esc(target.label)}</span>`
    : code(target.label);
  return target.href ? `<a href="${attr(target.href)}"${title}>${name}</a>` : name;
}

/** The body a card expands to: what the concept, proof, or submission page
 * leads with, so a reader can judge the passage without leaving the paper.
 * A concept's claims are listed only where there are several: the badge
 * in the card's head already says how a single claim stands. A proof's
 * description can be left out (`proofDescription: false`), leaving the
 * judgment alone. */
async function markBody(ctx: PageContext, mark: PaperMark, home: string, rootRel: string, options: { proofDescription?: boolean } = {}): Promise<string> {
  const { model, markdown } = ctx;
  if (mark.kind === "concept") {
    const located = model.conceptHome.get(mark.id);
    if (!located) return `<p class="empty-note">Not in this archive.</p>`;
    const { concept } = located;
    const statements = concept.statements.length > 1
      ? `<ul class="manuscript-card-claims">${concept.statements.map((s) => `<li>${claimEntry(model, s.id, rootRel, home, { role: "conclusion" })}</li>`).join("")}</ul>`
      : "";
    // The Lean source as the concept page shows it, minus the module
    // docstring (the description above already says it) and without row
    // anchors: the same concept may be marked more than once in a paper.
    const proven = new Set(concept.statements.map((s) => s.id).filter((id) => model.network.proven.has(id)));
    const rows = concept.sourceText.trim()
      ? await highlightSource(concept.sourceText, concept.statements, proven, { omitModuleDoc: true, anchors: false })
      : "";
    const source = rows
      ? `<div class="manuscript-card-source"><div class="inline-contract-wrap"><table class="inline-contract-table">
${rows}
</table></div></div>`
      : "";
    return `<p class="manuscript-card-title">${markdown.renderAuthorInline(concept.title, rootRel)}</p>
<div class="latex-content">${markdown.renderAuthorProse(concept.description, rootRel)}</div>
${statements}${source}`;
  }
  if (mark.kind === "proof") {
    const located = model.proofHome.get(mark.id);
    if (!located) return `<p class="empty-note">Not in this archive.</p>`;
    const description = options.proofDescription !== false && located.proof.description.trim()
      ? `<div class="latex-content">${markdown.renderAuthorProse(located.proof.description, rootRel)}</div>`
      : "";
    return `${proofJudgment(model, located.proof, rootRel, home)}${description}`;
  }
  const submission = model.submissionById.get(mark.id);
  const title = submission?.output?.manifest.title;
  return title
    ? `<p class="manuscript-card-title">${markdown.renderAuthorInline(title, rootRel)}</p>`
    : `<p class="empty-note">Not in this archive.</p>`;
}

/** One card, mark-numbered, in the vocabulary of the pages it links to.
 * On the printed page the card itself owns the `m<n>` id the cross-links
 * target; on the reflow page that id belongs to the passage's anchor in the
 * text, so the card steps aside to `m<n>-card`. Every card carries
 * `data-mark`, which is how the surface's script finds it in the rail.
 * The card sits beside its passage, so it does not say the page. The
 * landing page borrows the same card for its paper excerpt, with its own
 * id and the site root as `rootRel`. */
export async function markCard(
  ctx: PageContext,
  mark: PaperMark,
  n: number,
  home: string,
  cardId = `m${n}`,
  options: { rootRel?: string; expanded?: boolean; proofDescription?: boolean } = {},
): Promise<string> {
  const { model } = ctx;
  const rootRel = options.rootRel ?? "../";
  const expanded = options.expanded === true;
  return `<li class="manuscript-card kind-${mark.kind}${markStatus(model, mark)}${expanded ? " manuscript-card-expanded" : ""}" id="${cardId}" data-mark="${n}">
<div class="manuscript-card-head">
<span class="manuscript-card-swatch" aria-hidden="true"></span>
<span class="manuscript-card-name">${markBadge(model, mark)}${markName(model, mark, home, rootRel)}</span>
<button class="manuscript-card-toggle" type="button" aria-expanded="${expanded}" aria-controls="${attr(`${cardId}-body`)}" aria-label="${attr(`Show details of ${mark.id}`)}"><span aria-hidden="true">▸</span></button>
</div>
<div class="manuscript-card-body" id="${attr(`${cardId}-body`)}"${expanded ? "" : " hidden"}>
${await markBody(ctx, mark, home, rootRel, { proofDescription: options.proofDescription })}
</div>
</li>`;
}

/** The "In the paper" block of a concept or proof page — and the submission
 * page of a marked submission: each passage with its page, own paper
 * first, linking to the card. Empty when nothing marks the id. The
 * submission page asks for foreign papers only: its own is the button
 * above. */
export function inPaperBlock(ctx: PageContext, id: string, home: string, rootRel: string, options: { foreignOnly?: boolean } = {}): string {
  const mentions = [...(ctx.model.paperMentions.get(id) ?? [])].filter((m) => !options.foreignOnly || m.submission.record.id !== home).sort((a, b) => {
    const ownA = a.submission.record.id === home ? 0 : 1;
    const ownB = b.submission.record.id === home ? 0 : 1;
    return ownA - ownB || compareIds(a.submission.record.id, b.submission.record.id) || a.n - b.n;
  });
  if (!mentions.length) return "";
  const rows = mentions.map(({ submission, n, page: pageNumber }) => {
    const sid = submission.record.id;
    const href = `${rootRel}${sid}/paper.html#m${n}`;
    const where = sid === home
      ? "this submission's paper"
      : `the paper of <span class="submission-meta-id">${esc(sid)}</span>${submission.output ? `, ${ctx.markdown.renderAuthorInline(submission.output.manifest.title, rootRel)}` : ""}`;
    return `<li><a href="${attr(href)}">page ${pageNumber}</a> of ${where}</li>`;
  });
  return `<div class="block block-paper"><h3>In the paper</h3>
<ul class="in-paper-list">
${rows.join("\n")}
</ul>
</div>`;
}

/** Inert JSON for assets/manuscript.js: page sizes and the marks' points. */
function manuscriptData(submission: SiteSubmission): string {
  const paper = submission.output!.paper!;
  return inertJsonScript("manuscript-data", {
    pageSizes: paper.pageSizes,
    marks: paper.marks.map((mark, index) => ({ n: index + 1, id: mark.id, kind: mark.kind, begin: mark.begin, end: mark.end })),
  });
}

/** The AGPL §13 notice under the reflow surface: the software painting this
 * page runs in the reader's browser, so the page carries its source offer —
 * upstream for now; the lax-archive fork once that repository exists. The
 * vendored viewer's provenance header names the rev and the modifications. */
const REFLOW_NOTICE = `<footer class="manuscript-reflow-notice">Rendered with <a href="https://github.com/radek-p/reflowtex" rel="license">ReflowTeX</a> — free software under <abbr title="GNU Affero General Public License v3.0 or later">AGPL-3.0-or-later</abbr>. <a href="https://github.com/radek-p/reflowtex">Source code</a>.</footer>`;

type PaperView = "reflow" | "pdf";

/** The switch above a paper that has both surfaces: the reflowed text
 * first (it is what `paper.html` opens on), the paper as printed beside it,
 * the current one marked. Links, not buttons — each surface is its own
 * page — and the surface's script carries the `#m<n>` fragment across. */
function viewSwitch(current: PaperView): string {
  const link = (view: PaperView, href: string, label: string) =>
    `<a class="manuscript-view-link" href="${href}"${view === current ? ` aria-current="page"` : ""}>${label}</a>`;
  return `<div class="manuscript-view-switch" role="group" aria-label="Paper view">
${link("reflow", "paper.html", "Reflowed")}
${link("pdf", "paper-pdf.html", "As printed")}
</div>`;
}

/** The reflow surface: the viewer's schema and font-map islands, one
 * `.latex-block` per block (embedded, or fetched past the embed budget),
 * the cards rail its anchors join, and the template the script clones a
 * footnote's sidenote card from (one per footnote the viewer reveals). */
function reflowBody(cards: string[], web: PaperWebPage): string {
  const blocks = web.blocks.map((block) =>
    "b64" in block
      ? `<div class="latex-block" data-nodelist-b64="${block.b64}"></div>`
      : `<div class="latex-block" data-nodelist-src="${attr(block.src)}"></div>`);
  return `<div class="manuscript-body manuscript-reflow-body" id="manuscript-reflow">
<div class="manuscript-reflow-doc" id="manuscript-reflow-doc">
${blocks.join("\n")}
${REFLOW_NOTICE}
</div>
<ol class="manuscript-rail" id="manuscript-rail-reflow">
${cards.join("\n")}
</ol>
<svg class="manuscript-links" id="manuscript-reflow-links" aria-hidden="true"></svg>
<template id="manuscript-footnote-card"><li class="manuscript-card manuscript-footnote"><div class="manuscript-footnote-body"></div></li></template>
</div>
<noscript><p class="empty-note">Enable JavaScript to read the paper here, or <a href="paper.pdf">download the PDF</a>.</p></noscript>
<div id="latex-schema" data-schema-b64="${web.schemaB64}" hidden></div>
<script type="application/json" id="latex-font-map" data-fonts-base="../fonts/">${JSON.stringify(web.fontMap).replace(/</g, "\\u003c")}</script>`;
}

/** The printed surface: one box per page for pdf.js to fill, the cards
 * rail beside them, the gutter bands' overlay. */
function pdfBody(cards: string[], pages: string[]): string {
  return `<div class="manuscript-body">
<div class="manuscript-pages" id="manuscript-pages">
${pages.join("\n")}
</div>
<ol class="manuscript-rail" id="manuscript-rail">
${cards.join("\n")}
</ol>
<svg class="manuscript-links" id="manuscript-links" aria-hidden="true"></svg>
</div>
<p class="manuscript-status" id="manuscript-status" role="status">Loading the paper…</p>
<noscript><p class="empty-note">Enable JavaScript to read the paper here, or <a href="paper.pdf">download the PDF</a>.</p></noscript>`;
}

interface PaperPageOptions {
  /** The reflow bundle, for the reflow page. */
  web?: PaperWebPage;
  /** This is `paper-pdf.html`, titled as printed. */
  printed?: boolean;
  /** Whether a reflow page exists beside this printed page (the switch). */
  reflowBeside?: boolean;
}

async function renderPaper(ctx: PageContext, submission: SiteSubmission, options: PaperPageOptions): Promise<string> {
  const { record, output } = submission;
  const paper = output!.paper!;
  const home = record.id;
  const title = ctx.markdown.renderAuthorInline(output!.manifest.title, "../");
  const hasPdf = Boolean(submission.paperFile);
  const reflow = options.web !== undefined;
  const cards = await Promise.all(paper.marks.map((mark, index) =>
    markCard(ctx, mark, index + 1, home, reflow ? `m${index + 1}-card` : undefined)));
  const facts = [
    plural(paper.pdf.pages, "page"),
    plural(paper.marks.length, "marked passage"),
    esc(paper.engine),
    hasPdf ? `<a href="paper.pdf">download PDF</a>` : "",
    `<a href="index.html">${esc(home)}</a>`,
  ].filter(Boolean).join(" · ");

  let body: string;
  let rootAttributes = "";
  let scripts: string[];
  if (reflow) {
    body = viewSwitch("reflow") + "\n" + reflowBody(cards, options.web!);
    // The vendored viewer (self-contained — its lax fork decodes blocks
    // without protobuf.js), then the join glue.
    scripts = ["assets/version-history.js", "assets/reflowtex/latex-viewer.js", "assets/manuscript-reflow.js"];
  } else if (hasPdf) {
    const pages = paper.pageSizes.map(([width, height], index) =>
      `<div class="manuscript-page" data-page="${index + 1}" style="aspect-ratio: ${width} / ${height}"></div>`);
    body = (options.reflowBeside ? viewSwitch("pdf") + "\n" : "") + pdfBody(cards, pages) + "\n" + manuscriptData(submission);
    rootAttributes = ` data-pdf="paper.pdf" data-pdfjs="${attr(`../assets/pdfjs/pdf.min.mjs?v=${siteAssetVersion("pdfjs/pdf.min.mjs")}`)}" data-pdfjs-worker="${attr(`../assets/pdfjs/pdf.worker.min.mjs?v=${siteAssetVersion("pdfjs/pdf.worker.min.mjs")}`)}"`;
    // Placement math first, then the DOM and pdf.js glue that reads it.
    scripts = ["assets/version-history.js", "assets/manuscript-place.js", "assets/manuscript.js"];
  } else {
    body = `<p class="empty-note">The PDF is not part of preview builds; the published archive shows it here beside the cards.</p>
<ol class="manuscript-rail manuscript-rail-static">
${cards.join("\n")}
</ol>`;
    scripts = ["assets/version-history.js"];
  }

  const content = `${draftBanner(record.state)}${environmentNotice(ctx.model, submission)}${versionHistoryPanel(ctx, home, "../")}
<div class="manuscript"${rootAttributes}>
<div class="detail-heading concept-heading manuscript-heading">
<div><p class="concept-id">Paper</p>
<h1 class="concept-title">${title}</h1>
<p class="concept-microline">${facts}</p></div>
</div>
${body}
</div>`;

  return page({
    title: `${options.printed ? "Paper as printed" : "Paper"} — ${home}`,
    rootRel: "../",
    sidebar: submissionSidebar(ctx.model, submission, "../", { backToSubmission: true }),
    content,
    detailClass: "detail-manuscript",
    scripts,
  });
}

/** `paper.html`: the reflowed paper when the bundle is there, the paper as
 * printed otherwise (and the cards alone in a preview build). */
export function paperPage(ctx: PageContext, submission: SiteSubmission, web?: PaperWebPage): Promise<string> {
  return renderPaper(ctx, submission, { web });
}

/** `paper-pdf.html`: the paper as printed, emitted beside every cached
 * PDF so the printed rendering keeps one address whether or not a reflow
 * page stands in front of it. */
export function paperPdfPage(ctx: PageContext, submission: SiteSubmission, reflowBeside: boolean): Promise<string> {
  return renderPaper(ctx, submission, { printed: true, reflowBeside });
}
