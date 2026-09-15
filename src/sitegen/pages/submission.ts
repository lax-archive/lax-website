import { attr, esc, page, plural, typeBadge } from "../html.js";
import { DEFAULT_SITE_URL } from "../../config.js";
import { renderBibEntry } from "../bibtex.js";
import { conceptGraph, graphDataScript, submissionGraph, type SubmissionGraphData } from "../graphs.js";
import { compareIds, type LocatedConcept, type SiteSubmission } from "../model.js";
import { conceptReviewBadge, conceptReviewProgress, discussion, pageReactions } from "./discussion.js";
import { inPaperBlock } from "./paper.js";
import {
  anonymityNotice,
  bibtex,
  conceptMapLegend,
  draftBanner,
  environmentNotice,
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
  repositorySource,
  shortId,
  sourceLink,
  sourceProviderName,
  submissionMapLegend,
  submissionSidebar,
  withheldSourceLink,
} from "./shared.js";

/** All reviewable concepts whose correctness this submission relies on,
 * including transitive concept imports and concepts named by proofs. */
function submissionReviewConcepts(ctx: PageContext, submission: SiteSubmission): LocatedConcept[] {
  const output = submission.output!;
  const concepts = new Map<string, LocatedConcept>();
  const add = (id: string) => {
    const home = ctx.model.conceptHome.get(id) ?? ctx.model.statementHome.get(id);
    if (!home || concepts.has(home.concept.id)) return;
    concepts.set(home.concept.id, home);
    home.concept.imports.forEach(add);
  };
  output.concepts.forEach((concept) => add(concept.id));
  output.proofs.forEach((proof) => [proof.conclusion, ...proof.assumptions].forEach(add));
  return [...concepts.values()].sort((a, b) =>
    compareIds(a.output.id, b.output.id) || a.concept.id.localeCompare(b.concept.id));
}

function conceptPath({ submission, concept }: LocatedConcept): string {
  return `${submission.record.id}/${concept.id}.html`;
}

function countsTowardReviewProgress({ concept }: LocatedConcept): boolean {
  return concept.type?.trim().toLowerCase() !== "lemma";
}

/** Statements and definitions occupy separate rows of the concept grid. */
function conceptLists(ctx: PageContext, concepts: LocatedConcept[], home?: string): string {
  const list = (label: string, group: LocatedConcept[]) => group.length
    ? `<ul class="concept-list" aria-label="${attr(label)}">
${group.map(({ concept, submission }) => {
      const provenCount = concept.statements.filter((statement) => ctx.model.network.proven.has(statement.id)).length;
      const status = concept.statements.length ? provenCount === concept.statements.length : undefined;
      const pathname = `${submission.record.id}/${concept.id}.html`;
      const href = home ? `${concept.id}.html` : `../${pathname}`;
      // Archive ids use `lax-N`, while Lean namespaces use `LaxN`.
      // Normalize only the owning submission's display prefix; imported
      // concepts in the expandable list retain their full identifiers.
      const namespace = home?.replace(/^lax-(\d+)$/, "Lax$1");
      const name = home ? shortId(concept.id, namespace) : concept.id;
      return `<li>${typeBadge(concept.type, status)}<a href="${attr(href)}" title="${attr(concept.id)}"><code>${esc(name)}</code></a>${conceptReviewBadge(pathname)}</li>`;
    }).join("\n")}
</ul>`
    : "";
  return [
    list("Statements", concepts.filter(({ concept }) => concept.statements.length > 0)),
    list("Definitions", concepts.filter(({ concept }) => concept.statements.length === 0)),
  ].filter(Boolean).join("\n");
}

function usedConceptRows(ctx: PageContext, concepts: LocatedConcept[]): string {
  if (!concepts.length) return "";
  return `<button class="concept-used-toggle" type="button" data-used-concepts-toggle aria-controls="used-concepts-list" aria-expanded="false">Show referenced concepts</button>
<div class="concept-used-list" id="used-concepts-list" role="group" aria-label="Concepts used from other submissions" hidden>
${conceptLists(ctx, concepts)}
</div>`;
}

/** The submission page: abstract first, sleek meta, concepts with their DAG,
 * proofs with the proof network, citation, references. */
export function submissionPage(ctx: PageContext, submission: SiteSubmission): string {
  const { record, output } = submission;
  const sidebar = submissionSidebar(ctx.model, submission, "../");
  if (!output) {
    const content = `${draftBanner(record.state)}${environmentNotice(ctx.model, submission)}${versionHistoryPanel(ctx, record.id, "../", true)}
${paperHeader(ctx, submission, "../", versionHistoryMetaButton(ctx, record.id))}
${pageReactions(`${record.id}/`, { kind: "submission" })}
<p class="empty-note">No content uploaded yet. Run <code>lax build</code> and submit a draft.</p>
${discussion(`${record.id}/`)}`;
    return page({
      title: `${record.id} — Lax`,
      rootRel: "../",
      canonicalPath: `${record.id}/`,
      sidebar,
      sidebarState: "open",
      content,
      scripts: ["assets/version-history.js", "assets/comments.js"],
    });
  }

  const anonymous = output.manifest.anonymous === true;
  // Build each figure's data once so its legend and embedded JSON describe
  // exactly the same nodes and edges.
  const related = submissionGraph(ctx.model, output.id);
  const graphs = pageGraphData(ctx, submission, related);
  const reviewedConcepts = submissionReviewConcepts(ctx, submission);
  const usedConcepts = reviewedConcepts.filter((located) => located.output.id !== output.id);
  const reviewedConceptPaths = reviewedConcepts.map(conceptPath);
  const ownConcepts = output.concepts.map((concept) => ({ submission, output, concept }));
  const listedConcepts: LocatedConcept[] = [...ownConcepts, ...usedConcepts];
  const progressConceptPaths = listedConcepts.filter(countsTowardReviewProgress).map(conceptPath);
  const externalConcepts = usedConceptRows(ctx, usedConcepts);
  const concepts = conceptLists(ctx, ownConcepts, output.id);
  const proofsHref = proofsSource(submission);
  const proofsSourceWithheld = anonymous && Boolean(record.source);
  const proofRows = output.proofs.map((proof) =>
    proofItem(ctx.model, { submission, output, proof }, "../", { anchorId: `p-${proof.id}`, home: output.id }));
  const hasReferences = output.manifest.bibEntries.length > 0;
  const references = anonymous
    ? ""
    : output.manifest.bibEntries.map((entry) => renderBibEntry(entry)).join("\n");
  // A submission alone in its corner of the archive gets a sentence, not an
  // empty figure: the map only says something once there is a neighbour.
  const relatedFigure = related.nodes.length > 1
    ? `${figureTitle("Submission map")}
<figure class="graph-figure">
${graphExpandButton("submission map")}
<div id="submission-dag" class="figure-container" data-graph="submissions"></div>
${graphTooltip()}
${submissionMapLegend(related)}
</figure>`
    : `<p class="empty-note">No other submission in the archive builds on this one, and this one builds on none.</p>`;

  const content = `${draftBanner(record.state)}${environmentNotice(ctx.model, submission)}${versionHistoryPanel(ctx, record.id, "../", true)}
${paperHeader(ctx, submission, "../", versionHistoryMetaButton(ctx, record.id))}
${pageReactions(`${record.id}/`, { kind: "submission", conceptPaths: reviewedConceptPaths, anonymous })}
${output.abstract.trim() ? paperAbstract(ctx.markdown.renderAuthorProse(output.abstract, "../")) : ""}
${paperSection(ctx, submission)}
<section class="page-section"><h3 class="section-title">Concepts</h3>
${output.concepts.length || usedConcepts.length ? `<div class="concept-list-box">
${conceptReviewProgress(progressConceptPaths)}
${concepts}
${externalConcepts}
</div>` : `<p class="empty-note">No concepts in this submission.</p>`}
${output.concepts.length ? `<details class="figure-details">
<summary>Concept map</summary>
<figure class="graph-figure">
${graphExpandButton("concept map", true)}
<div id="concept-dag" class="figure-container" data-graph="concepts" data-ancestry="true"></div>
${graphTooltip()}
${conceptMapLegend(graphs.concepts, "This submission", "Other submission")}
</figure>
</details>` : ""}
</section>
<section class="page-section"><h3 class="section-title">Proofs</h3>
${output.proofs.length ? `${figureTitle("Proof network", proofsHref, proofsSourceWithheld)}
<figure class="graph-figure proof-network-figure">
${graphExpandButton("proof network")}
<div id="proof-network" class="figure-container" data-graph="proofs"></div>
${graphTooltip()}
${proofNetworkLegend(graphs.proofs)}
</figure>
<details class="figure-details">
<summary>Proof list</summary>
<div class="proof-list-box">
<ul class="proof-list">
${proofRows.join("\n")}
</ul>
${proofsHref
    ? `<p class="proof-list-source">Lean sources for these proofs: ${sourceLink(proofsHref, `proofs/ on ${sourceProviderName(proofsHref)}`)}</p>`
    : proofsSourceWithheld
      ? `<p class="proof-list-source">Lean sources for these proofs: ${withheldSourceLink("withheld during anonymous review")}</p>`
      : ""}
</div>
<p class="honesty-note">Proof code is not displayed; the archive records each proof's checked relationship between claims.</p>
</details>` : `<p class="empty-note">No proofs in this submission.</p>`}
</section>
<section class="page-section"><h3 class="section-title">Related submissions</h3>
${relatedFigure}
</section>
<section class="page-section"><h3 class="section-title" id="citation">Cite this</h3>
<p class="honesty-note">This is only the formalizers. The authors of the formalized results may be different (see References).</p>
${anonymous
    ? anonymityNotice("Citation withheld", "A citation exists for this submission, but it is unavailable during anonymous review.")
    : `<div class="citation-box">
<pre class="citation" id="submission-citation">${esc(bibtex(ctx.model, submission))}</pre>
<button class="citation-copy" type="button" data-copy-citation aria-controls="submission-citation" aria-label="Copy BibTeX to clipboard" title="Copy BibTeX"><span class="citation-copy-icon" aria-hidden="true"></span></button>
<output class="citation-copy-status" aria-live="polite"></output>
</div>`}
</section>
${hasReferences
    ? anonymous
      ? `<section class="page-section"><h3 class="section-title">References</h3>\n${anonymityNotice("References withheld", "References are present, but they are unavailable during anonymous review.")}\n</section>`
      : `<section class="page-section"><h3 class="section-title">References</h3>\n<ol class="reference-list">\n${references}\n</ol>\n</section>`
    : ""}
${discussion(`${record.id}/`)}
${graphDataScript(graphs)}`;
  return page({
    title: `${output.manifest.title} — ${record.id}`,
    rootRel: "../",
    canonicalPath: `${record.id}/`,
    sidebar,
    sidebarState: "open",
    content,
    noIndex: output.manifest.unlisted === true,
    scripts: ["assets/graph-interaction.js", ...(anonymous ? [] : ["assets/citation.js"]), "assets/version-history.js", "assets/comments.js"],
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

/** Graph data for graph-interaction.js, embedded as inert JSON (CSP-safe). Concept data
 * contains the page's own concepts plus both closures behind the toggles;
 * proof data is the submission's upstream statement/proof closure;
 * submission data is the same dependency question one level up. */
function pageGraphData(ctx: PageContext, submission: SiteSubmission, related: SubmissionGraphData) {
  const output = submission.output!;
  const own = new Set(output.concepts.map((c) => c.id));
  const concepts = conceptGraph(ctx.model, own);
  // Keep the page home in the permitted presentation payload; node labels
  // are prepared from their titles before browser interaction runs.
  return {
    concepts: { ...concepts, home: output.id },
    proofs: proofNetworkData(ctx, submission, "../"),
    submissions: related,
  };
}

/** The proof network figure's data: the submission's own statements and
 * proofs, plus the complete upstream closure of archived proofs. `rootRel`
 * prefixes the node links — the landing page draws a submission's network
 * from the site root. */
export function proofNetworkData(ctx: PageContext, submission: SiteSubmission, rootRel: string) {
  const output = submission.output!;
  const model = ctx.model;
  const namespace = output.id.replace(/^lax-(\d+)$/, "Lax$1");
  const ownStatements = new Set(output.concepts.flatMap((c) => c.statements.map((s) => s.id)));
  const statementIds = new Set<string>();
  const pendingStatements: string[] = [];
  const proofs = new Map<string, {
    id: string;
    assumptions: string[];
    conclusion: string;
    description: string;
    owner: string;
    ext: boolean;
  }>();

  const addStatement = (id: string) => {
    if (statementIds.has(id)) return;
    statementIds.add(id);
    pendingStatements.push(id);
  };
  const addProof = (proof: typeof output.proofs[number], owner: string) => {
    if (proofs.has(proof.id)) return;
    for (const id of [proof.conclusion, ...proof.assumptions]) addStatement(id);
    proofs.set(proof.id, {
      id: proof.id,
      assumptions: proof.assumptions,
      conclusion: proof.conclusion,
      description: proof.description,
      owner,
      ext: owner !== output.id,
    });
  };

  for (const id of ownStatements) addStatement(id);
  for (const proof of output.proofs) addProof(proof, output.id);
  for (let index = 0; index < pendingStatements.length; index += 1) {
    const statementId = pendingStatements[index]!;
    for (const { proof, output: home } of model.statementProofs.get(statementId) ?? []) {
      addProof(proof, home.id);
    }
  }
  // Every sibling statement of a displayed concept comes along, so the figure
  // can draw one dock per statement — each with its own status — even where no
  // displayed proof touches it. A whole-concept assumption stays one coarse
  // incidence; bringing its statements along never expands that assumption.
  for (const id of [...statementIds])
    for (const sibling of (model.statementHome.get(id) ?? model.conceptHome.get(id))?.concept.statements ?? [])
      statementIds.add(sibling.id);
  const statementNodes = [...statementIds].sort().map((id) => {
    const statementHome = model.statementHome.get(id);
    const home = statementHome ?? model.conceptHome.get(id);
    const conceptEndpoint = !statementHome && home !== undefined;
    const siblings = home?.concept.statements ?? [];
    const index = siblings.findIndex((statement) => statement.id === id) + 1;
    const proven = conceptEndpoint
      ? siblings.length > 0 && siblings.every((statement) => model.network.proven.has(statement.id))
      : model.network.proven.has(id);
    return {
      id,
      // A claim displays as its home concept. `index`/`count` place it inside
      // a multi-statement concept, which the figure draws as one box with a
      // numbered dock per statement.
      // Shorten only this submission's visible labels; semantic IDs and
      // references to other submissions keep their full namespaces.
      label: home?.output.id === output.id ? shortId(home.concept.id, namespace) : home?.concept.id,
      title: home?.concept.title,
      tooltipHtml: ctx.markdown.renderAuthorTooltip(home?.concept.title ?? "", rootRel),
      owner: home?.output.id,
      concept: home?.concept.id,
      ...(conceptEndpoint ? { endpointKind: "concept" as const, status: siblings.length ? proven ? "proven" as const : "open" as const : "none" as const } : {}),
      index: index || undefined,
      count: home ? siblings.length : undefined,
      href: home ? `${rootRel}${home.output.id}/${home.concept.id}.html${statementHome ? `#s-${id}` : ""}` : undefined,
      proven,
      ext: home ? home.output.id !== output.id : !ownStatements.has(id),
    };
  });
  const proofNodes = [...proofs.values()]
    .sort((a, b) => a.id.localeCompare(b.id))
    .map((proof) => {
      const outstanding = proof.assumptions.filter((id) => !model.network.proven.has(id));
      return {
        ...proof,
        tooltipHtml: ctx.markdown.renderAuthorTooltip(proof.description, rootRel),
        href: model.proofHome.has(proof.id)
          ? `${rootRel}${model.proofHome.get(proof.id)!.output.id}/${proof.id}.html`
          : undefined,
        assumptionsProven: outstanding.length === 0,
        outstanding: outstanding.length,
      };
    });

  const canonicalPageUrl = (pathname: string) =>
    new URL(pathname.replace(/^\/+/, ""), `${DEFAULT_SITE_URL.replace(/\/+$/, "")}/`).toString();
  const submissionDetails = (home: SiteSubmission) => {
    const id = home.output?.id ?? home.record.id;
    const name = home.output?.manifest.title ?? home.record.id;
    return {
      id: home.record.id,
      name,
      nameHtml: ctx.markdown.renderAuthorInline(name, rootRel),
      state: home.record.state,
      ...(id !== output.id ? { href: `${rootRel}${id}/index.html` } : {}),
    };
  };
  const authorSections = (sections: { title: string; markdown: string }[] | undefined) =>
    (sections ?? []).map((section) => ({
      titleHtml: ctx.markdown.renderAuthorInline(section.title, rootRel),
      bodyHtml: ctx.markdown.renderAuthorProse(section.markdown, rootRel),
    }));
  const claimSummary = (id: string) => {
    const home = model.statementHome.get(id);
    const conceptHome = home ?? model.conceptHome.get(id);
    if (!home && conceptHome) {
      const statements = conceptHome.concept.statements;
      return {
        id,
        name: conceptHome.concept.title,
        nameHtml: ctx.markdown.renderAuthorInline(conceptHome.concept.title, rootRel),
        href: `${rootRel}${conceptHome.output.id}/${conceptHome.concept.id}.html`,
        proven: statements.length === 0 || statements.every((statement) => model.network.proven.has(statement.id)),
      };
    }
    if (!home) return { id, name: id, proven: false };
    const index = home.concept.statements.findIndex((statement) => statement.id === id) + 1;
    return {
      id,
      name: home.concept.title,
      nameHtml: ctx.markdown.renderAuthorInline(home.concept.title, rootRel),
      href: `${rootRel}${home.output.id}/${home.concept.id}.html#s-${id}`,
      proven: model.network.proven.has(id),
      statement: home.concept.statements.length > 1 ? index : undefined,
      statementCount: home.concept.statements.length,
    };
  };
  const openAssumptionsInTree = (roots: readonly string[]) => {
    const open = new Set<string>(), seen = new Set<string>(), pending = [...roots];
    while (pending.length) {
      const id = pending.pop()!;
      if (seen.has(id)) continue;
      seen.add(id);
      for (const { proof } of model.statementProofs.get(id) ?? []) {
        for (const assumption of proof.assumptions) {
          if (!model.network.proven.has(assumption)) open.add(assumption);
          pending.push(assumption);
        }
      }
    }
    return [...open].sort(compareIds);
  };
  const details: Record<string, unknown> = {};
  for (const id of [...statementIds].sort()) {
    const home = model.statementHome.get(id) ?? model.conceptHome.get(id);
    if (!home || details[`concept:${home.concept.id}`]) continue;
    const { concept, output: conceptOutput, submission: conceptSubmission } = home;
    const provenCount = concept.statements.filter((statement) => model.network.proven.has(statement.id)).length;
    const openAssumptionIds = openAssumptionsInTree(concept.statements.map((statement) => statement.id));
    details[`concept:${concept.id}`] = {
      kind: "concept",
      name: concept.title,
      nameHtml: ctx.markdown.renderAuthorInline(concept.title, rootRel),
      type: concept.type,
      status: concept.statements.length === 0 ? "none"
        : provenCount === concept.statements.length ? "proven" : "open",
      statusDetail: concept.statements.length === 0 ? "Definition"
        : `${provenCount} of ${concept.statements.length} statement${concept.statements.length === 1 ? "" : "s"} proven`,
      openAssumptions: openAssumptionIds.length,
      openAssumptionIds,
      submission: submissionDetails(conceptSubmission),
      anonymousReview: conceptSubmission.output?.manifest.anonymous === true,
      descriptionHtml: ctx.markdown.renderAuthorProse(concept.description, rootRel),
      statements: concept.statements.map((statement, index) => ({
        id: statement.id,
        name: concept.statements.length > 1 ? `${index + 1} of ${concept.statements.length}` : "Lean statement",
        signature: statement.signature,
        proven: model.network.proven.has(statement.id),
        href: `${rootRel}${conceptOutput.id}/${concept.id}.html#s-${statement.id}`,
      })),
      sections: authorSections(concept.sections),
      href: `${rootRel}${conceptOutput.id}/${concept.id}.html`,
      reviewUrl: canonicalPageUrl(`${conceptSubmission.record.id}/${concept.id}.html`),
      reviewLabel: "Theorem review",
    };
  }
  for (const proof of proofNodes) {
    const home = model.proofHome.get(proof.id);
    const proofSubmission = home?.submission ?? submission;
    const conclusion = claimSummary(proof.conclusion);
    const conclusionHome = model.statementHome.get(proof.conclusion);
    const anonymous = proofSubmission.output?.manifest.anonymous === true;
    const source = anonymous ? undefined : proofSubmission.record.source;
    const sourceHref = source && home
      ? repositorySource(source.repository, source.commit, source.folder, home.proof.path)
      : undefined;
    details[`proof:${proof.id}`] = {
      kind: "proof",
      name: `Proof of ${conclusion.name}`,
      nameHtml: `Proof of ${ctx.markdown.renderAuthorInline(conclusion.name, rootRel)}`,
      status: proof.assumptionsProven ? "grounded" : "conditional",
      statusDetail: proof.assumptionsProven
        ? "All assumptions are proven"
        : `${proof.outstanding} open assumption${proof.outstanding === 1 ? "" : "s"}`,
      submission: submissionDetails(proofSubmission),
      anonymousReview: conclusionHome?.submission.output?.manifest.anonymous === true,
      descriptionHtml: ctx.markdown.renderAuthorProse(proof.description, rootRel),
      sections: authorSections(home?.proof.sections),
      conclusion,
      assumptions: proof.assumptions.map(claimSummary),
      leanPath: anonymous ? undefined : home?.proof.path,
      sourceHref,
      href: proof.href,
      reviewUrl: conclusionHome
        ? canonicalPageUrl(`${conclusionHome.submission.record.id}/${conclusionHome.concept.id}.html`)
        : undefined,
      reviewLabel: "Conclusion review",
    };
  }

  return { statements: statementNodes, proofs: proofNodes, details, home: output.id };
}
