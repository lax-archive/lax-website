import { attr, esc, page, plural, typeBadge } from "../html.js";
import { renderBibEntry } from "../bibtex.js";
import { conceptGraph, graphDataScript, submissionGraph, type SubmissionGraphData } from "../graphs.js";
import type { SiteSubmission } from "../model.js";
import { discussion, pageReactions } from "./discussion.js";
import { inPaperBlock } from "./paper.js";
import {
  bibtex,
  conceptBadgeLegend,
  conceptMapLegend,
  draftBanner,
  versionHistoryMetaButton,
  versionHistoryPanel,
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
  sourceProviderName,
  submissionMapLegend,
  submissionSidebar,
} from "./shared.js";

/** The submission page: abstract first, sleek meta, concepts with their DAG,
 * proofs with the proof network, citation, references. */
export function submissionPage(ctx: PageContext, submission: SiteSubmission): string {
  const { record, output } = submission;
  const sidebar = submissionSidebar(ctx.model, submission, "../");
  if (!output) {
    const content = `${draftBanner(record.state)}${versionHistoryPanel(ctx, record.id, "../", true)}
${paperHeader(ctx.markdown, submission, "../", versionHistoryMetaButton(ctx, record.id))}
${pageReactions(`${record.id}/`, { kind: "submission" })}
<p class="empty-note">No content uploaded yet. Run <code>lax build</code> and submit a draft.</p>
${discussion(`${record.id}/`)}`;
    return page({
      title: `${record.id} — Lax`,
      rootRel: "../",
      sidebar,
      content,
      scripts: ["assets/version-history.js", "assets/comments.js"],
    });
  }

  const proven = ctx.model.network.proven;
  // Build each figure's data once so its legend and embedded JSON describe
  // exactly the same nodes and edges.
  const related = submissionGraph(ctx.model, output.id);
  const graphs = pageGraphData(ctx, submission, related);
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
  const relatedFigure = related.nodes.length > 1
    ? `${figureTitle("Submission map")}
<figure class="graph-figure">
<div id="submission-dag" class="figure-container" data-graph="submissions"></div>
${graphTooltip()}
${submissionMapLegend()}
</figure>`
    : `<p class="empty-note">No other submission in the archive builds on this one, and this one builds on none.</p>`;

  const content = `${draftBanner(record.state)}${versionHistoryPanel(ctx, record.id, "../", true)}
${paperHeader(ctx.markdown, submission, "../", versionHistoryMetaButton(ctx, record.id))}
${pageReactions(`${record.id}/`, { kind: "submission" })}
${output.abstract.trim() ? paperAbstract(ctx.markdown.renderAuthorProse(output.abstract, "../")) : ""}
${paperSection(ctx, submission)}
<section class="page-section"><h3 class="section-title">Concepts</h3>
${output.concepts.length ? `<div class="concept-list-box">
<ul class="concept-list">
${conceptRows.join("\n")}
</ul>
${conceptBadgeLegend(graphs.concepts.nodes.filter((node) => !node.ext).map((node) => node.status))}
</div>
${figureTitle("Concept map")}
<figure class="graph-figure">
${graphExpandButton("concept map")}
<div class="graph-toolbar"><button type="button" id="concept-expand" aria-controls="concept-dag" aria-pressed="true">Hide ancestors</button><button type="button" id="concept-descend" aria-controls="concept-dag" aria-pressed="false">Show descendants</button><output id="concept-graph-status" aria-live="polite"></output></div>
<div id="concept-dag" class="figure-container" data-graph="concepts" data-ancestry="true"></div>
${graphTooltip()}
${conceptMapLegend(graphs.concepts, "This submission", "Other submission")}
</figure>` : `<p class="empty-note">No concepts in this submission.</p>`}
</section>
<section class="page-section"><h3 class="section-title">Proofs</h3>
${output.proofs.length ? `<div class="proof-list-box">
<ul class="proof-list">
${proofRows.join("\n")}
</ul>
${proofsHref ? `<p class="proof-list-source">Lean sources for these proofs: ${sourceLink(proofsHref, `proofs/ on ${sourceProviderName(proofsHref)}`)}</p>` : ""}
</div>
${figureTitle("Proof network", proofsHref)}
<figure class="graph-figure proof-network-figure">
${graphExpandButton("proof network")}
<div id="proof-network" class="figure-container" data-graph="proofs"></div>
${graphTooltip()}
${proofNetworkLegend(graphs.proofs)}
</figure>` : `<p class="empty-note">No proofs in this submission.</p>`}
<p class="honesty-note">Proof code is not displayed; the archive records each proof's checked relationship between claims.</p>
</section>
<section class="page-section"><h3 class="section-title">Related submissions</h3>
${relatedFigure}
</section>
<section class="page-section"><h3 class="section-title" id="citation">Cite this</h3>
<div class="citation-box">
<pre class="citation" id="submission-citation">${esc(bibtex(ctx.model, submission))}</pre>
<button class="citation-copy" type="button" data-copy-citation aria-controls="submission-citation" aria-label="Copy BibTeX to clipboard" title="Copy BibTeX"><span class="citation-copy-icon" aria-hidden="true"></span></button>
<output class="citation-copy-status" aria-live="polite"></output>
</div>
</section>
${references ? `<section class="page-section"><h3 class="section-title">References</h3>\n<ol class="reference-list">\n${references}\n</ol>\n</section>` : ""}
${discussion(`${record.id}/`)}
${graphDataScript(graphs)}`;
  return page({
    title: `${output.manifest.title} — ${record.id}`,
    rootRel: "../",
    sidebar,
    content,
    scripts: ["assets/layout.js", "assets/dag.js", "assets/citation.js", "assets/version-history.js", "assets/comments.js"],
  });
}

/** The way into the annotated paper, right after the abstract: one
 * centered button with the page and passage counts under it. Below,
 * where *other* papers mark this submission. */
function paperSection(ctx: PageContext, submission: SiteSubmission): string {
  const { record, output } = submission;
  const paper = output!.paper;
  const mentions = inPaperBlock(ctx, record.id, record.id, "../", { foreignOnly: true });
  if (!paper) return mentions;
  return `<section class="page-section paper-cta">
<a class="source-button paper-cta-button" href="paper.html"><span>View annotated paper</span></a>
<p class="paper-cta-facts">${plural(paper.pdf.pages, "page")} · ${plural(paper.marks.length, "marked passage")}</p>
</section>
${mentions}`;
}

/** Graph data for dag.js, embedded as inert JSON (CSP-safe). Concept data
 * contains the page's own concepts plus both closures behind the toggles;
 * proof data is the submission's bipartite statement/proof neighborhood;
 * submission data is the same dependency question one level up. */
function pageGraphData(ctx: PageContext, submission: SiteSubmission, related: SubmissionGraphData) {
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
  // Every sibling statement of a displayed concept comes along, so the figure
  // can draw one dock per statement — each with its own status — even where no
  // displayed proof touches it.
  for (const id of [...statementIds])
    for (const sibling of model.statementHome.get(id)?.concept.statements ?? [])
      statementIds.add(sibling.id);
  const statementNodes = [...statementIds].sort().map((id) => {
    const home = model.statementHome.get(id);
    const siblings = home?.concept.statements ?? [];
    const index = siblings.findIndex((statement) => statement.id === id) + 1;
    return {
      id,
      // A claim displays as its home concept; the raw statement id stays
      // available for the tooltip. `index`/`count` place the statement inside
      // a multi-statement concept, which the figure draws as one box with a
      // numbered dock per statement.
      label: home?.concept.id,
      title: home?.concept.title,
      owner: home?.output.id,
      concept: home?.concept.id,
      index: index || undefined,
      count: home ? siblings.length : undefined,
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
  return {
    concepts: { ...concepts, home: output.id },
    proofs: { statements: statementNodes, proofs: proofNodes, home: output.id },
    submissions: related,
  };
}
