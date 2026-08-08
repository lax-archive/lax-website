import { attr, esc, page, typeBadge } from "../html.js";
import { renderBibEntry } from "../bibtex.js";
import { conceptGraph, graphDataScript, submissionGraph, type SubmissionGraphData } from "../graphs.js";
import type { SiteSubmission } from "../model.js";
import {
  bibtex,
  conceptBadgeLegend,
  conceptMapLegend,
  draftBanner,
  figureTitle,
  graphExpandButton,
  graphTooltip,
  paperAbstract,
  paperHeader,
  type PageContext,
  proofItem,
  proofNetworkLegend,
  proofsSource,
  shortId,
  sourceLink,
  submissionMapLegend,
  submissionSidebar,
} from "./shared.js";

/** The submission page: abstract first, sleek meta, concepts with their DAG,
 * proofs with the proof network, citation, references. */
export function submissionPage(ctx: PageContext, submission: SiteSubmission): string {
  const { record, output } = submission;
  const sidebar = submissionSidebar(ctx.model, submission, "../");
  if (!output) {
    const content = `${draftBanner(record.state)}
${paperHeader(ctx.markdown, submission, "../")}
<p class="empty-note">No content uploaded yet. Run <code>lax build</code> and submit a draft.</p>`;
    return page({ title: `${record.id} — Lax`, rootRel: "../", sidebar, content });
  }

  const proven = ctx.model.network.proven;
  const conceptRows = output.concepts.map((concept) => {
    const provenCount = concept.statements.filter((s) => proven.has(s.id)).length;
    const status = concept.statements.length ? provenCount === concept.statements.length : undefined;
    const name = shortId(concept.id, output.id);
    return `<li>${typeBadge(concept.type, status)}<a href="${attr(`${concept.id}.html`)}" title="${attr(concept.id)}"><code>${esc(name)}</code></a></li>`;
  });
  const proofsHref = proofsSource(submission);
  const proofRows = output.proofs.map((proof) =>
    proofItem(ctx.model, { submission, output, proof }, "../", { anchorId: `p-${proof.id}`, home: output.id }));
  const references = output.manifest.bibEntries
    .map((entry) => renderBibEntry(entry))
    .join("\n");
  // A submission alone in its corner of the archive gets a sentence, not an
  // empty figure: the map only says something once there is a neighbour.
  const related = submissionGraph(ctx.model, output.id);
  const relatedFigure = related.nodes.length > 1
    ? `${figureTitle("Submission map")}
<figure class="graph-figure">
<div id="submission-dag" class="figure-container" data-graph="submissions"></div>
${graphTooltip()}
${submissionMapLegend()}
</figure>`
    : `<p class="empty-note">No other submission in the archive builds on this one, and this one builds on none.</p>`;

  const content = `${draftBanner(record.state)}
${paperHeader(ctx.markdown, submission, "../")}
${output.abstract.trim() ? paperAbstract(ctx.markdown.renderAuthorProse(output.abstract, "../")) : ""}
<section class="page-section"><h3 class="section-title">Concepts</h3>
${output.concepts.length ? `<div class="concept-list-box">
<ul class="concept-list">
${conceptRows.join("\n")}
</ul>
${conceptBadgeLegend()}
</div>
${figureTitle("Concept map")}
<figure class="graph-figure">
${graphExpandButton("concept map")}
<div class="graph-toolbar"><button type="button" id="concept-expand" aria-controls="concept-dag" aria-pressed="true">Hide ancestors</button><button type="button" id="concept-descend" aria-controls="concept-dag" aria-pressed="false">Show descendants</button><output id="concept-graph-status" aria-live="polite"></output></div>
<div id="concept-dag" class="figure-container" data-graph="concepts" data-ancestry="true"></div>
${graphTooltip()}
${conceptMapLegend("This submission", "Other submission")}
</figure>` : `<p class="empty-note">No concepts in this submission.</p>`}
</section>
<section class="page-section"><h3 class="section-title">Proofs</h3>
${output.proofs.length ? `<div class="proof-list-box">
<ul class="proof-list">
${proofRows.join("\n")}
</ul>
${proofsHref ? `<p class="proof-list-source">Lean sources for these proofs: ${sourceLink(proofsHref, "proofs/ on GitHub")}</p>` : ""}
</div>
${figureTitle("Proof network", proofsHref)}
<figure class="graph-figure">
${graphExpandButton("proof network")}
<div id="proof-network" class="figure-container" data-graph="proofs"></div>
${graphTooltip()}
${proofNetworkLegend()}
</figure>` : `<p class="empty-note">No proofs in this submission.</p>`}
<p class="honesty-note">Proof code is not displayed; the archive records each proof's checked relationship between claims.</p>
</section>
<section class="page-section"><h3 class="section-title">Related submissions</h3>
${relatedFigure}
</section>
<section class="page-section"><h3 class="section-title" id="citation">Cite this</h3>
<div class="citation-box">
<pre class="citation" id="submission-citation">${esc(bibtex(submission))}</pre>
<button class="citation-copy" type="button" data-copy-citation aria-controls="submission-citation" aria-label="Copy BibTeX to clipboard" title="Copy BibTeX"><span class="citation-copy-icon" aria-hidden="true"></span></button>
<output class="citation-copy-status" aria-live="polite"></output>
</div>
</section>
${references ? `<section class="page-section"><h3 class="section-title">References</h3>\n<ol class="reference-list">\n${references}\n</ol>\n</section>` : ""}
${graphData(ctx, submission, related)}`;
  return page({
    title: `${output.manifest.title} — ${record.id}`,
    rootRel: "../",
    sidebar,
    content,
    scripts: ["assets/layout.js", "assets/dag.js", "assets/citation.js"],
  });
}

/** Graph data for dag.js, embedded as inert JSON (CSP-safe). Concept data
 * contains the page's own concepts plus both closures behind the toggles;
 * proof data is the submission's bipartite statement/proof neighborhood;
 * submission data is the same dependency question one level up. */
function graphData(ctx: PageContext, submission: SiteSubmission, related: SubmissionGraphData): string {
  const output = submission.output!;
  const model = ctx.model;
  const own = new Set(output.concepts.map((c) => c.id));
  const concepts = conceptGraph(model, own);

  // Proof network: own statements and proofs, plus external proofs that
  // conclude an own statement. Keep every assumption of those external
  // proofs so the displayed hyperedge is never made misleadingly easier.
  const ownStatements = new Set(output.concepts.flatMap((c) => c.statements.map((s) => s.id)));
  const statementIds = new Set<string>(ownStatements);
  const proofs = new Map<string, {
    id: string;
    assumptions: string[];
    conclusion: string;
    description: string;
    owner: string;
    ext: boolean;
  }>();
  for (const proof of output.proofs) {
    for (const id of [proof.conclusion, ...proof.assumptions]) statementIds.add(id);
    proofs.set(proof.id, {
      id: proof.id,
      assumptions: proof.assumptions,
      conclusion: proof.conclusion,
      description: proof.description,
      owner: output.id,
      ext: false,
    });
  }
  for (const statementId of ownStatements) {
    for (const { proof, output: home } of model.statementProofs.get(statementId) ?? []) {
      if (home.id === output.id) continue;
      for (const id of [proof.conclusion, ...proof.assumptions]) statementIds.add(id);
      proofs.set(proof.id, {
        id: proof.id,
        assumptions: proof.assumptions,
        conclusion: proof.conclusion,
        description: proof.description,
        owner: home.id,
        ext: true,
      });
    }
  }
  const statementNodes = [...statementIds].sort().map((id) => {
    const home = model.statementHome.get(id);
    return {
      id,
      // One-statement rule: the claim displays as its home concept; the raw
      // statement id stays available for the tooltip.
      label: home?.concept.id,
      title: home?.concept.title,
      owner: home?.output.id,
      href: home ? `../${home.output.id}/${home.concept.id}.html#s-${id}` : undefined,
      proven: model.network.proven.has(id),
      ext: !ownStatements.has(id),
    };
  });
  const proofNodes = [...proofs.values()]
    .sort((a, b) => a.id.localeCompare(b.id))
    .map((proof) => {
      const outstanding = proof.assumptions.filter((id) => !model.network.proven.has(id));
      return {
        ...proof,
        href: model.proofHome.has(proof.id)
          ? `../${model.proofHome.get(proof.id)!.output.id}/${proof.id}.html`
          : undefined,
        assumptionsProven: outstanding.length === 0,
        outstanding: outstanding.length,
      };
    });

  // `home` lets dag.js shorten the page's own concept ids to bare names.
  const data = {
    concepts: { ...concepts, home: output.id },
    proofs: { statements: statementNodes, proofs: proofNodes, home: output.id },
    submissions: related,
  };
  return graphDataScript(data);
}
