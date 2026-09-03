import { attr, code, countsPill, esc, page } from "../html.js";
import { conceptGraph, graphDataScript } from "../graphs.js";
import { highlightSource } from "../highlight.js";
import type { LocatedConcept } from "../model.js";
import { discussion, pageReactions } from "./discussion.js";
import { inPaperBlock } from "./paper.js";
import {
  conceptLink,
  conceptMapLegend,
  conceptShortName,
  draftBanner,
  figureTitle,
  ordinal,
  shortId,
  versionHistoryPanel,
  repositorySource,
  graphExpandButton,
  graphTooltip,
  type PageContext,
  proofItem,
  sourceProviderName,
  submissionSidebar,
} from "./shared.js";

const MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs/";

/** Statement ranges include their leading documentation. Find the declaration
 * row so a proof action can be positioned beside the axiom itself. */
function statementDeclarationLine(source: string, start?: number, end?: number): number | undefined {
  if (start === undefined || end === undefined) return start;
  const lines = source.split("\n");
  for (let line = start; line <= end; line++) {
    if (/^\s*(?:axiom|theorem|lemma)\b/.test(lines[line - 1] ?? "")) return line;
  }
  return start;
}

/** The evidence block of a claim-concept: every archived proof concluding
 * this claim, each relative to its own assumptions — "true relative to what".
 * Definition-concepts (no statement) claim nothing and get no block; an open
 * claim says so explicitly. A concept declaring several statements gets one
 * sub-block per statement, each named by its anonymous position. */
function evidence(ctx: PageContext, located: LocatedConcept): string {
  const { output, concept } = located;
  if (!concept.statements.length) return "";
  const proofsOf = (statementId: string) =>
    (ctx.model.statementProofs.get(statementId) ?? []).map((proof) =>
      proofItem(ctx.model, proof, "../", { origin: proof.output.id !== output.id, home: output.id }));
  const list = (items: string[], empty: string) => items.length
    ? `<ul class="proof-list">\n${items.join("\n")}\n</ul>`
    : `<p class="empty-note">${empty}</p>`;
  const block = (intro: string, body: string) => `<div class="block block-evidence"><h3>Evidence</h3>
<p class="evidence-intro">${intro}</p>
${body}
</div>`;
  if (concept.statements.length === 1)
    return block(
      "Each proof establishes this claim relative to its assumptions.",
      list(proofsOf(concept.statements[0]!.id), "No proof in the archive yet — this claim is open."),
    );
  const proven = ctx.model.network.proven;
  const blocks = concept.statements.map((statement, index) => {
    const heading = `<a href="#s-${attr(statement.id)}">${esc(ordinal(index + 1))} statement</a> ${code(shortId(statement.id, concept.id))} ${countsPill(proven.has(statement.id) ? 1 : 0, 1)}`;
    return `<div class="evidence-statement"><h4>${heading}</h4>
${list(proofsOf(statement.id), "No proof in the archive yet — this statement is open.")}
</div>`;
  });
  return block(
    `This concept declares ${concept.statements.length} statements. Each proof establishes one of them relative to its assumptions.`,
    blocks.join("\n"),
  );
}

/** The concept page: NL block under the type heading, the full Lean module as
 * a line-numbered table, extra annotation sections, statements, dependencies. */
export async function conceptPage(ctx: PageContext, located: LocatedConcept): Promise<string> {
  const { submission, output, concept } = located;
  const proven = ctx.model.network.proven;
  const provenCount = concept.statements.filter((s) => proven.has(s.id)).length;
  const graph = conceptGraph(ctx.model, [concept.id]);
  const source = submission.record.source;
  const sourceFile = source
    ? repositorySource(source.repository, source.commit, source.folder, concept.path)
    : undefined;

  const type = concept.type!.trim();
  const typeHeading = type.charAt(0).toUpperCase() + type.slice(1);

  const sections = (concept.sections ?? [])
    .map((s) => `<div class="block"><h3>${ctx.markdown.renderAuthorInline(s.title, "../")}</h3><div class="latex-content">${ctx.markdown.renderAuthorProse(s.markdown, "../")}</div></div>`)
    .join("\n");

  const importRows = concept.imports.map((id) => `<li>${conceptLink(ctx.model, id, "../", output.id)}</li>`);
  const mathlibRows = (concept.mathlibImports ?? []).map((id) =>
    `<li><a href="${attr(`${MATHLIB_DOCS}${id.replace(/\./g, "/")}.html`)}">${code(id)}</a></li>`);
  const usedByRows = (ctx.model.importers.get(concept.id) ?? []).map((item) =>
    `<li>${conceptLink(ctx.model, item.concept.id, "../", output.id)}</li>`);
  const depsCol = (heading: string, rows: string[]) =>
    `<div class="deps-col"><h3>${esc(heading)}</h3>${rows.length ? `<ul class="deps-list">${rows.join("")}</ul>` : `<p class="empty-note">none</p>`}</div>`;

  // One rail per statement that has proofs, anchored at that statement's own
  // declaration row; source-proof.js groups rails by row, so several of them
  // on one page position independently.
  const proofActions = concept.statements.map((statement) => {
    const declarationLine = statementDeclarationLine(concept.sourceText, statement.startLine, statement.endLine);
    const proofLinks = (ctx.model.statementProofs.get(statement.id) ?? []).flatMap(({ submission: proofSubmission, proof }) => {
      const proofSource = proofSubmission.record.source;
      const href = proofSource
        ? repositorySource(proofSource.repository, proofSource.commit, proofSource.folder, proof.path)
        : undefined;
      return href ? [{ id: proof.id, href, provider: sourceProviderName(href) }] : [];
    });
    if (!proofLinks.length || declarationLine === undefined) return "";
    return `<span class="source-proof-rail" data-source-line="L${declarationLine}" aria-label="Proof links">${proofLinks.map((link, index) => {
      const label = proofLinks.length === 1 ? "Show Proof" : `Show Proof ${index + 1}`;
      return `<a class="statement-proof-button" href="${attr(link.href)}" aria-label="${attr(`View proof ${link.id} on ${link.provider}`)}" title="${attr(link.id)}"><span class="statement-proof-mark" aria-hidden="true">⊢</span><span class="statement-proof-label">${label}</span><span class="statement-proof-arrow" aria-hidden="true">→</span></a>`;
    }).join("")}</span>`;
  }).join("");
  const sourceRows = await highlightSource(concept.sourceText, concept.statements, proven);

  const content = `${versionHistoryPanel(ctx, submission.record.id, "../")}${draftBanner(submission.record.state)}
<div class="detail-heading concept-heading">
<div><p class="concept-id"><code>${esc(concept.id)}</code></p>
<h1 class="concept-title">${ctx.markdown.renderAuthorInline(concept.title, "../")}</h1>
<p class="concept-microline"><code>${esc(concept.path)}</code> · <a href="index.html">${esc(output.id)}</a></p></div>
<span class="status-pills">${countsPill(provenCount, concept.statements.length)}</span>
</div>
${pageReactions(`${submission.record.id}/${concept.id}.html`, { kind: "concept", sourceLines: concept.sourceText.split("\n").length })}
${figureTitle("Concept map")}
<figure class="graph-figure concept-root-graph">
${graphExpandButton("concept map")}
<div class="graph-toolbar"><button type="button" id="concept-expand" aria-controls="concept-dag" aria-pressed="true">Hide ancestors</button><button type="button" id="concept-descend" aria-controls="concept-dag" aria-pressed="false">Show descendants</button><output id="concept-graph-status" aria-live="polite"></output></div>
<div id="concept-dag" class="figure-container" data-graph="concepts" data-ancestry="true"></div>
${graphTooltip()}
${conceptMapLegend(graph, "This concept", "Related concept")}
</figure>
${evidence(ctx, located)}
${inPaperBlock(ctx, concept.id, output.id, "../")}
<div class="block block-statement"><h3>${esc(typeHeading)}</h3><div class="latex-content">${ctx.markdown.renderAuthorProse(concept.description, "../")}</div></div>
<div class="block block-lean"><h3 class="section-heading">Lean source${sourceFile ? ` <a class="source-link" href="${attr(sourceFile)}">view on ${esc(sourceProviderName(sourceFile))}</a>` : ""}</h3>
<div class="inline-contract-shell"><div class="inline-contract-wrap"><table class="inline-contract-table">
${sourceRows}
</table></div>${proofActions}<span class="source-review-rails" data-source-review-rails aria-label="Source flags"></span></div></div>
${sections}
<div class="block"><div class="deps-columns">
${depsCol("Builds on", importRows)}
${depsCol("Used by", usedByRows)}
${depsCol("From Mathlib", mathlibRows)}
</div></div>
${discussion(`${submission.record.id}/${concept.id}.html`)}
${graphDataScript({
    concepts: { ...graph, home: output.id },
    proofs: { statements: [], proofs: [] },
  })}`;

  return page({
    title: `${concept.title} — ${conceptShortName(output, concept)}`,
    rootRel: "../",
    sidebar: submissionSidebar(ctx.model, submission, "../", { activeId: concept.id }),
    content,
    scripts: ["assets/layout.js", "assets/dag.js", "assets/source-proof.js", "assets/version-history.js", "assets/comments.js"],
  });
}
