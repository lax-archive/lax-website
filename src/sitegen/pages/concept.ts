import { attr, code, countsPill, esc, page } from "../html.js";
import { conceptGraph, graphDataScript } from "../graphs.js";
import { highlightSource } from "../highlight.js";
import type { LocatedConcept } from "../model.js";
import {
  conceptLink,
  conceptMapLegend,
  conceptShortName,
  draftBanner,
  figureTitle,
  githubSource,
  graphTooltip,
  type PageContext,
  proofItem,
  submissionSidebar,
} from "./shared.js";

const MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs/";

/** The evidence block of a claim-concept: every archived proof concluding
 * this claim, each relative to its own assumptions — "true relative to what".
 * Definition-concepts (no statement) claim nothing and get no block; an open
 * claim says so explicitly. */
function evidence(ctx: PageContext, located: LocatedConcept): string {
  const { output, concept } = located;
  const statement = concept.statements[0];
  if (!statement) return "";
  if (concept.statements.length > 1)
    throw new Error(`concept ${concept.id} declares ${concept.statements.length} statements; the one-statement rule admits at most one`);
  const items = (ctx.model.statementProofs.get(statement.id) ?? []).map((proof) =>
    proofItem(ctx.model, proof, "../", { origin: proof.output.id !== output.id, home: output.id }));
  const body = items.length
    ? `<ul class="proof-list">\n${items.join("\n")}\n</ul>`
    : `<p class="empty-note">No proof in the archive yet — this claim is open.</p>`;
  return `<div class="block block-evidence"><h3>Evidence</h3>
<p class="evidence-intro">Each proof establishes this claim relative to its assumptions.</p>
${body}
</div>`;
}

/** The concept page: NL block under the type heading, the full Lean module as
 * a line-numbered table, extra annotation sections, statements, dependencies. */
export async function conceptPage(ctx: PageContext, located: LocatedConcept): Promise<string> {
  const { submission, output, concept } = located;
  const proven = ctx.model.network.proven;
  const provenCount = concept.statements.filter((s) => proven.has(s.id)).length;
  const source = submission.record.source;
  const githubFile = source
    ? githubSource(source.repository, source.commit, source.folder, concept.path)
    : undefined;

  const type = concept.type!.trim();
  const typeHeading = type.charAt(0).toUpperCase() + type.slice(1);

  const sections = (concept.sections ?? [])
    .map((s) => `<div class="block"><h3>${esc(s.title)}</h3><div class="latex-content">${ctx.markdown.renderAuthorProse(s.markdown, "../")}</div></div>`)
    .join("\n");

  const importRows = concept.imports.map((id) => `<li>${conceptLink(ctx.model, id, "../", output.id)}</li>`);
  const mathlibRows = (concept.mathlibImports ?? []).map((id) =>
    `<li><a href="${attr(`${MATHLIB_DOCS}${id.replace(/\./g, "/")}.html`)}">${code(id)}</a></li>`);
  const usedByRows = (ctx.model.importers.get(concept.id) ?? []).map((item) =>
    `<li>${conceptLink(ctx.model, item.concept.id, "../", output.id)}</li>`);
  const depsCol = (heading: string, rows: string[]) =>
    `<div class="deps-col"><h3>${esc(heading)}</h3>${rows.length ? `<ul class="deps-list">${rows.join("")}</ul>` : `<p class="empty-note">none</p>`}</div>`;

  const sourceRows = await highlightSource(concept.sourceText, concept.statements, proven);

  const content = `${draftBanner(submission.record.state)}
<div class="detail-heading concept-heading">
<div><p class="concept-id"><code>${esc(concept.id)}</code></p>
<h1 class="concept-title">${esc(concept.title)}</h1>
<p class="concept-microline"><code>${esc(concept.path)}</code> · <a href="index.html">${esc(output.id)}</a></p></div>
<span class="status-pills">${countsPill(provenCount, concept.statements.length)}</span>
</div>
${figureTitle("Concept map")}
<figure class="graph-figure concept-root-graph">
<div class="graph-toolbar"><button type="button" id="concept-expand" aria-controls="concept-dag" aria-pressed="true">Hide ancestors</button><button type="button" id="concept-descend" aria-controls="concept-dag" aria-pressed="false">Show descendants</button><output id="concept-graph-status" aria-live="polite"></output></div>
<div id="concept-dag" class="figure-container" data-graph="concepts" data-ancestry="true"></div>
${graphTooltip()}
${conceptMapLegend("This concept", "Related concept")}
</figure>
${evidence(ctx, located)}
<div class="block block-statement"><h3>${esc(typeHeading)}</h3><div class="latex-content">${ctx.markdown.renderAuthorProse(concept.description, "../")}</div></div>
<div class="block block-lean"><h3 class="section-heading">Lean source${githubFile ? ` <a class="source-link" href="${attr(githubFile)}">view on GitHub</a>` : ""}</h3>
<div class="inline-contract-shell"><div class="inline-contract-wrap"><table class="inline-contract-table">
${sourceRows}
</table></div></div></div>
${sections}
<div class="block"><div class="deps-columns">
${depsCol("Builds on", importRows)}
${depsCol("Used by", usedByRows)}
${depsCol("From Mathlib", mathlibRows)}
</div></div>
${graphDataScript({
    concepts: { ...conceptGraph(ctx.model, [concept.id]), home: output.id },
    proofs: { statements: [], proofs: [] },
  })}`;

  return page({
    title: `${concept.title} — ${conceptShortName(output, concept)}`,
    rootRel: "../",
    sidebar: submissionSidebar(ctx.model, submission, "../", { activeId: concept.id }),
    content,
    scripts: ["assets/layout.js", "assets/dag.js"],
  });
}
