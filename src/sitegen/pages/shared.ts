import { DEFAULT_SITE_URL } from "../../config.js";
import type { BuildOutput, ConceptEntry, ProofEntry } from "../../types.js";
import type { ConceptGraphData } from "../graphs.js";
import { attr, code, esc, formatDate, proofBadge, statePill, typeBadge } from "../html.js";
import type { MarkdownRenderer } from "../markdown.js";
import { compareIds, type LocatedProof, type SiteModel, type SiteSubmission } from "../model.js";

export interface PageContext { model: SiteModel; markdown: MarkdownRenderer }

// ---- display names ----

/** Identifiers on a page belonging to submission `home` drop the `home.`
 * prefix — the same rule dag.js applies to graph node labels: the repetition
 * is noise, and the full id stays available in tooltips and hrefs. */
export function shortId(id: string, home?: string): string {
  return home && id.startsWith(home + ".") ? id.slice(home.length + 1) : id;
}

// ---- cross-page links ----

function conceptHref(model: SiteModel, id: string, rootRel: string): string | undefined {
  const home = model.conceptHome.get(id);
  return home ? `${rootRel}${home.output.id}/${home.concept.id}.html` : undefined;
}

export function conceptLink(model: SiteModel, id: string, rootRel: string, home?: string): string {
  const href = conceptHref(model, id, rootRel);
  const label = shortId(id, home);
  const title = label === id ? "" : ` title="${attr(id)}"`;
  return href ? `<a href="${attr(href)}"${title}>${code(label)}</a>` : code(id);
}

// ---- proofs as judgments between claims ----

/** A statement rendered as its home claim-concept (one-statement rule: the
 * concept *is* the claim): type badge with the proven mark, linked to the
 * concept page. Every statement a proof names must resolve — a missing home
 * means a corrupt or incomplete database, not something to render around. */
export function claimEntry(model: SiteModel, statementId: string, rootRel: string, pageHome?: string): string {
  const home = model.statementHome.get(statementId);
  if (!home) throw new Error(`statement ${statementId} has no home concept in the archive`);
  const proven = model.network.proven.has(statementId);
  const href = `${rootRel}${home.output.id}/${home.concept.id}.html`;
  return `<span class="claim-entry">${typeBadge(home.concept.type, proven)}<a href="${attr(href)}" title="${attr(statementId)}">${code(shortId(home.concept.id, pageHome))}</a></span>`;
}

/** The judgment card: assumptions boxed on the left, an arrow, the concluded
 * claim on the right — the checked relationship a proof contributes. */
export function proofJudgment(model: SiteModel, proof: ProofEntry, rootRel: string, pageHome?: string): string {
  const assumptions = proof.assumptions.length
    ? `<ul>${proof.assumptions.map((id) => `<li>${claimEntry(model, id, rootRel, pageHome)}</li>`).join("\n")}</ul>`
    : `<p class="judgment-unconditional">no assumptions</p>`;
  return `<div class="judgment">
<div class="judgment-assumptions">${assumptions}</div>
<span class="judgment-arrow" aria-hidden="true">→</span>
<div class="judgment-conclusion">${claimEntry(model, proof.conclusion, rootRel, pageHome)}</div>
</div>`;
}

/** One proof in a list: the judgment card leads (its whole surface links to
 * the proof page via an overlay; the claim links inside stay clickable), the
 * proof id follows below. `origin` names the home submission (for foreign
 * proofs); the description stays on the proof page. */
export function proofItem(
  model: SiteModel,
  located: LocatedProof,
  rootRel: string,
  opts: { anchorId?: string; origin?: boolean; home?: string } = {},
): string {
  const { output, proof } = located;
  const href = `${rootRel}${output.id}/${proof.id}.html`;
  const origin = opts.origin
    ? `<span class="proof-item-origin">from <a href="${attr(`${rootRel}${output.id}/index.html`)}">${esc(output.id)}</a></span>`
    : "";
  const name = proofShortName(output, proof, opts.home);
  const title = name === proof.id ? "" : ` title="${attr(proof.id)}"`;
  return `<li class="proof-item"${opts.anchorId ? ` id="${attr(opts.anchorId)}"` : ""}>
<div class="judgment-frame">
<a class="judgment-overlay" href="${attr(href)}" aria-label="${attr(`Open proof ${proof.id}`)}"></a>
${proofJudgment(model, proof, rootRel, opts.home)}
</div>
<p class="proof-item-head">${proofBadge()}<a class="proof-item-link" href="${attr(href)}"${title}>${code(name)}</a>${origin}</p>
</li>`;
}

/** A proof's display name on its home submission's pages: the spec mandates
 * the proof package be named `<id>Proofs`, so that prefix carries no more
 * information than the page it appears on. Foreign proofs keep the full id. */
export function proofShortName(output: BuildOutput, proof: ProofEntry, pageHome?: string): string {
  if (pageHome !== output.id) return proof.id;
  return shortId(proof.id, `${output.id}Proofs`);
}

// ---- graph figure furniture ----
// One legend grammar for both figures: fill = proven status, stroke = origin.

type ClaimStatus = ConceptGraphData["nodes"][number]["status"];

interface ProofNetworkLegendData {
  statements: { id: string; proven: boolean; ext: boolean }[];
  proofs: { id: string; assumptions: string[]; conclusion: string; ext: boolean }[];
}

/** Keep the status axis in one archive-wide order while omitting fills that
 * do not occur in this particular list or graph. */
function claimFillLegend(statuses: Iterable<ClaimStatus>, definitions = false): string {
  const present = new Set(statuses);
  return [
    present.has("proven") ? `<span><i class="legend-node fill-proven"></i>Proven claim</span>` : "",
    present.has("open") ? `<span><i class="legend-node fill-open"></i>Open claim</span>` : "",
    definitions && present.has("none") ? `<span><i class="legend-node fill-none"></i>Definition</span>` : "",
  ].join("");
}

/** The browser marks a cycle when the displayed bipartite claim/proof graph
 * has a directed cycle. Collapsing each claim -> proof -> claim step to a
 * claim edge gives the same answer without duplicating the layout code. */
function proofNetworkHasCycle(data: ProofNetworkLegendData): boolean {
  const statementIds = new Set(data.statements.map((statement) => statement.id));
  const successors = new Map([...statementIds].map((id) => [id, [] as string[]]));
  for (const proof of data.proofs) {
    if (!statementIds.has(proof.conclusion)) continue;
    for (const assumption of proof.assumptions)
      if (statementIds.has(assumption)) successors.get(assumption)!.push(proof.conclusion);
  }

  const visiting = new Set<string>();
  const visited = new Set<string>();
  const visit = (id: string): boolean => {
    if (visiting.has(id)) return true;
    if (visited.has(id)) return false;
    visiting.add(id);
    for (const next of successors.get(id)!) if (visit(next)) return true;
    visiting.delete(id);
    visited.add(id);
    return false;
  };
  return [...statementIds].some(visit);
}

/** The floating tooltip that dag.js positions inside a graph figure. */
export function graphTooltip(): string {
  return `<div class="graph-tooltip" role="tooltip" hidden></div>`;
}

/** Top-right control that lets dag.js present a graph as a large modal-like
 * window without duplicating its SVG or weakening the page CSP. */
export function graphExpandButton(label: string): string {
  return `<button class="graph-expand" type="button" data-graph-expand data-graph-label="${attr(label)}" aria-expanded="false" aria-label="${attr(`Open ${label} in a large window`)}" title="Open in large window"><svg class="graph-expand-open" viewBox="0 0 16 16" width="15" height="15" aria-hidden="true"><path d="M2.5 6V2.5H6M10 2.5h3.5V6M13.5 10v3.5H10M6 13.5H2.5V10"/></svg><span class="graph-expand-close" aria-hidden="true">×</span></button>`;
}

/** A figure's heading, in the text flow above the box like every other
 * heading — boxes hold content and controls, never their own title. */
export function figureTitle(title: string, source?: string): string {
  return `<h4 class="figure-title">${esc(title)}${source ? sourceLink(source) : ""}</h4>`;
}

/** The concept-list legend: what the badge letters, marks, and tints mean.
 * Sample badges are the real component, so the legend cannot drift. */
export function conceptBadgeLegend(statuses: Iterable<ClaimStatus>): string {
  const present = new Set(statuses);
  const items = [
    present.has("proven") ? `<span>${typeBadge("theorem", true)}proven claim</span>` : "",
    present.has("open") ? `<span>${typeBadge("theorem", false)}open claim</span>` : "",
    present.has("none") ? `<span>${typeBadge("definition")}definition</span>` : "",
  ];
  return `<div class="badge-legend" aria-label="Concept badge legend">${items.join("")}</div>`;
}

export function conceptMapLegend(data: ConceptGraphData, ownLabel: string, extLabel: string): string {
  const items = [
    claimFillLegend(data.nodes.map((node) => node.status), true),
    data.nodes.some((node) => !node.ext) ? `<span><i class="legend-node stroke-own"></i>${esc(ownLabel)}</span>` : "",
    data.nodes.some((node) => node.ext) ? `<span><i class="legend-node stroke-ext"></i>${esc(extLabel)}</span>` : "",
    data.edges.length ? `<span><i class="legend-arrow" aria-hidden="true">→</i>A → B: B builds on A</span>` : "",
  ];
  return `<figcaption class="graph-legend" aria-label="Concept map legend">${items.join("")}</figcaption>`;
}

/** The submission map's legend. Same grammar one level up: stroke = origin,
 * arrow = direction of dependency. Submissions carry no proven/open status of
 * their own, so the fill axis stays out of it. */
export function submissionMapLegend(): string {
  return `<figcaption class="graph-legend" aria-label="Submission map legend"><span><i class="legend-node stroke-own"></i>This submission</span><span><i class="legend-node stroke-ext"></i>Other submission</span><span><i class="legend-arrow" aria-hidden="true">→</i>A → B: B builds on A</span></figcaption>`;
}

export function proofNetworkLegend(data: ProofNetworkLegendData): string {
  const statuses = data.statements.map((statement) => statement.proven ? "proven" as const : "open" as const);
  const nodes = [...data.statements, ...data.proofs];
  const items = [
    data.proofs.length ? `<span class="proof-flow">assumptions <i class="legend-arrow" aria-hidden="true">→</i><i class="legend-proof-chip" aria-hidden="true">⊢</i><i class="legend-arrow" aria-hidden="true">→</i> conclusion</span>` : "",
    claimFillLegend(statuses),
    nodes.some((node) => !node.ext) ? `<span><i class="legend-node stroke-own"></i>This submission</span>` : "",
    nodes.some((node) => node.ext) ? `<span><i class="legend-node stroke-ext"></i>From another submission</span>` : "",
    data.proofs.length ? `<span><i class="legend-proof-chip" aria-hidden="true">⊢</i>Proof — click to open</span>` : "",
    proofNetworkHasCycle(data) ? `<span><i class="legend-cycle"></i>Cycle — claims proving each other</span>` : "",
  ];
  return `<figcaption class="graph-legend" aria-label="Proof network legend">${items.join("")}</figcaption>`;
}

// ---- source links ----
// The site never displays proof code, so the link out to the repository is
// the only way to read it: it appears as a quiet inline link where a surface
// is merely adjacent to the code, and as a button where it is the page's
// main remaining action.

/** The GitHub mark, inline so it needs no img-src and no asset. Path from
 * GitHub's Octicons (MIT). */
const GITHUB_MARK =
  `<svg class="gh-mark" viewBox="0 0 16 16" width="15" height="15" aria-hidden="true" focusable="false"><path fill="currentColor" d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27s1.36.09 2 .27c1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.012 8.012 0 0 0 16 8c0-4.42-3.58-8-8-8Z"/></svg>`;

/** A quiet inline "view on GitHub" link, for headings and figure titles. */
export function sourceLink(href: string, label = "view on GitHub"): string {
  return `<a class="source-link" href="${attr(href)}">${esc(label)}</a>`;
}

/** The prominent variant: a bordered button carrying the GitHub mark. */
export function sourceButton(href: string, label: string): string {
  return `<a class="source-button" href="${attr(href)}">${GITHUB_MARK}<span>${esc(label)}</span></a>`;
}

/** The GitHub link to a submission's whole proof package — `proofs/` is a
 * fixed part of the submission layout. Undefined off github.com. */
export function proofsSource(submission: SiteSubmission): string | undefined {
  const source = submission.record.source;
  if (!source) return undefined;
  // `proofs/` goes in as part of the folder rather than as the path, so the
  // link comes out as a tree link — the path argument means a file.
  const folder = source.folder === "." ? "proofs" : `${source.folder.replace(/\/+$/, "")}/proofs`;
  return githubSource(source.repository, source.commit, folder);
}

/** A GitHub deep link for a source triple, or undefined off github.com. */
export function githubSource(
  repository: string,
  commit: string,
  folder: string,
  path = "",
  line?: number,
): string | undefined {
  if (!/^https:\/\/github\.com\//i.test(repository)) return undefined;
  const repo = repository.replace(/\.git$/, "").replace(/\/$/, "");
  const pieces = [folder === "." ? "" : folder, path]
    .filter(Boolean)
    .map((p) => p.replace(/^\/+|\/+$/g, ""));
  const href = `${repo}/${path ? "blob" : "tree"}/${commit}/${pieces.join("/")}`;
  return line ? `${href}#L${line}` : href;
}

// ---- sidebars ----

/** A concept's sidebar display name: the id without the package prefix. */
export function conceptShortName(output: BuildOutput, concept: ConceptEntry): string {
  const prefix = output.id + ".";
  return concept.id.startsWith(prefix) ? concept.id.slice(prefix.length) : concept.id;
}

const EMPTY_ROW = `<li id="entry-list-empty" hidden>No entries match.</li>`;

function searchGroup(placeholder = "Filter entries", controls = "entry-list"): string {
  return `<div class="filter-group">
<label for="filter-search">Search</label>
<input id="filter-search" class="filter-input" type="search" placeholder="${attr(placeholder)}" aria-controls="${attr(controls)}">
</div>`;
}

function submissionStateRank(state: string): number {
  if (state === "registered") return 0;
  if (state === "draft") return 1;
  return 2;
}

/** Registered submissions lead drafts both before and during search. Archive
 * ids break ties so the generated order is stable and unsurprising. */
export function compareSearchSubmissions(a: SiteSubmission, b: SiteSubmission): number {
  return submissionStateRank(a.record.state) - submissionStateRank(b.record.state)
    || compareIds(a.record.id, b.record.id);
}

/** Search metadata shared by the index sidebar and the full library. The
 * browser keeps submission title/id words separate from concept names so it
 * can rank title hits first without shipping a second search index. */
export function submissionSearchAttributes(
  submission: SiteSubmission,
  order: number,
  tags: string[] = [],
): string {
  const output = submission.output!;
  const title = `${submission.record.id} ${output.manifest.title}`.toLowerCase();
  const concepts = output.concepts
    .flatMap((concept) => [concept.id, concept.title, concept.type ?? ""])
    .join(" ")
    .toLowerCase();
  const tagKeys = tags.length ? `|${tags.join("|")}|` : "";
  return `data-search-title="${attr(title)}" data-search-concepts="${attr(concepts)}" data-state="${attr(submission.record.state)}" data-search-order="${order}" data-tags="${attr(tagKeys)}"`;
}

/** A homepage-only progressive-enhancement card. The first submission is a
 * deterministic no-JavaScript fallback; sidebar.js replaces it with a
 * randomly selected candidate when the page loads. */
function randomSubmissionView(
  model: SiteModel,
  markdown: MarkdownRenderer,
): string {
  const listed = currentSubmissions(model);
  if (!listed.length) return "";
  const candidate = (submission: SiteSubmission, dataAttribute = "") => {
    const id = submission.record.id;
    const title = submission.output!.manifest.title;
    return `<a href="${attr(`${id}/index.html`)}"${dataAttribute}><span class="random-submission-title">${markdown.renderAuthorInline(title, "")}</span><span class="random-submission-action">View submission <b aria-hidden="true">→</b></span></a>`;
  };
  return `<section class="random-submission" aria-labelledby="random-submission-heading">
<h2 id="random-submission-heading">Explore a random submission</h2>
${candidate(listed[0]!, " data-random-submission-link")}
<div class="random-submission-candidates" hidden aria-hidden="true">
${listed.map((submission) => candidate(submission, " data-random-submission-candidate")).join("\n")}
</div>
</section>`;
}

/** Sidebar of the index page: every current submission with content,
 * searchable. Superseded versions stay reachable from the version history
 * on their successors instead of competing with current work here.
 * Records that only reserved an id have nothing to show and stay off the
 * lists (their pages exist for direct links). Registered and draft work live
 * in labeled groups; all rows use their title as the visible label. */
export function indexSidebar(
  model: SiteModel,
  markdown: MarkdownRenderer,
  tagsBySubmission = new Map<string, string[]>(),
): string {
  const listed = currentSubmissions(model);
  const rows = listed.map((submission, order) => {
    const id = submission.record.id;
    const title = submission.output!.manifest.title;
    return `<li ${submissionSearchAttributes(submission, order, tagsBySubmission.get(id))}><a class="entry-link" href="${attr(id)}/index.html" data-full-title="${attr(title)}"><span class="entry-label"><span class="entry-label-text">${markdown.renderAuthorInline(title, "")}</span></span></a></li>`;
  });
  const draftStart = listed.findIndex((submission) => submission.record.state === "draft");
  if (draftStart >= 0)
    rows.splice(draftStart, 0, '<li class="entry-heading" data-entry-group="draft">Work in Progress</li>');
  if (listed.some((submission) => submission.record.state === "registered"))
    rows.unshift('<li class="entry-heading" data-entry-group="registered">Registered</li>');
  return `<div class="sidebar-filters">${searchGroup("Search titles and concepts", "entry-list submissions-list")}</div>
${randomSubmissionView(model, markdown)}
<ul id="entry-list">
${rows.join("\n")}
${EMPTY_ROW}
</ul>`;
}

/** Current listable submissions in the shared search order. Historical
 * versions are intentionally discoverable only through their version chain. */
export function currentSubmissions(model: SiteModel): SiteSubmission[] {
  return model.submissions
    .filter((submission) => submission.output && !model.isSuperseded(submission.record.id))
    .sort(compareSearchSubmissions);
}

/** Sidebar of submission, concept, and proof pages: back-link, search, type
 * filter, the submission's concepts (with the same status badges as the
 * concept list on the submission page), and its proofs below them. */
export function submissionSidebar(
  model: SiteModel,
  submission: SiteSubmission,
  rootRel: string,
  opts: { activeId?: string; backToSubmission?: boolean } = {},
): string {
  const output = submission.output;
  const concepts = output?.concepts ?? [];
  const proofs = output?.proofs ?? [];
  const proven = model.network.proven;
  const types = [...new Set(concepts.map((c) => c.type!.trim().toLowerCase()))].sort();
  const typeOptions = [...types, ...(proofs.length ? ["proof"] : [])]
    .map((t) => `<option value="${attr(t)}">${esc(t)}</option>`)
    .join("\n");
  const typeFilter = `<div class="filter-group">
<label for="filter-type">Type</label>
<select id="filter-type" class="filter-select">
<option value="all">All types</option>
${typeOptions}
</select>
</div>`;
  const conceptRows = concepts.map((concept) => {
    const name = conceptShortName(output!, concept);
    const type = concept.type!.trim().toLowerCase();
    const provenCount = concept.statements.filter((s) => proven.has(s.id)).length;
    const status = concept.statements.length ? provenCount === concept.statements.length : undefined;
    const haystack = `${concept.id} ${concept.title} ${type}`.toLowerCase();
    const active = concept.id === opts.activeId ? ' class="active"' : "";
    const href = `${rootRel}${submission.record.id}/${concept.id}.html`;
    return `<li${active} data-type="${attr(type)}" data-search="${attr(haystack)}"><a class="entry-link" href="${attr(href)}" data-full-title="${attr(concept.title)}"><span class="entry-label">${typeBadge(concept.type, status)}<span class="entry-label-text">${esc(name)}</span></span></a></li>`;
  });
  const proofRows = proofs.map((proof) => {
    const name = proofShortName(output!, proof, output!.id);
    const haystack = `${proof.id} proof`.toLowerCase();
    const active = proof.id === opts.activeId ? ' class="active"' : "";
    const href = `${rootRel}${submission.record.id}/${proof.id}.html`;
    return `<li${active} data-type="proof" data-search="${attr(haystack)}"><a class="entry-link" href="${attr(href)}" data-full-title="${attr(proof.id)}"><span class="entry-label">${proofBadge()}<span class="entry-label-text">${esc(name)}</span></span></a></li>`;
  });
  const rows = [
    ...(conceptRows.length && proofRows.length ? [`<li class="entry-heading" aria-hidden="true">Concepts</li>`] : []),
    ...conceptRows,
    ...(proofRows.length ? [`<li class="entry-heading" aria-hidden="true">Proofs</li>`] : []),
    ...proofRows,
  ];
  const onSubPage = Boolean(opts.activeId) || Boolean(opts.backToSubmission);
  const backHref = onSubPage ? `${rootRel}${submission.record.id}/index.html` : `${rootRel}index.html`;
  const backLabel = onSubPage ? submission.record.id : "All submissions";
  return `<a class="sidebar-back" href="${attr(backHref)}"><span class="sidebar-back-arrow" aria-hidden="true">←</span>${esc(backLabel)}</a>
<div class="sidebar-filters">${searchGroup()}
${typeFilter}</div>
<ul id="entry-list">
${rows.join("\n")}
${EMPTY_ROW}
</ul>`;
}

// ---- shared fragments ----

export function draftBanner(state: string): string {
  return state === "draft"
    ? `<p class="draft-banner"><strong>Draft</strong> — mutable and not usable as a dependency; its citation marks the draft state.</p>`
    : "";
}

function versionHref(rootRel: string, id: string): string {
  return `${rootRel}${id}/index.html?version=${encodeURIComponent(id)}`;
}

/** Version-history UI containing the complete chain. Superseded and proposed
 * versions get a prominent summary; the current submission page opts into
 * only the modal because its compact trigger lives in the metadata line. The
 * current registered version and the version shown on this page are distinct
 * states and are both marked. */
export function versionHistoryPanel(
  ctx: PageContext,
  submissionId: string,
  rootRel: string,
  includeCurrentDialog = false,
): string {
  const chain = ctx.model.versionHistory(submissionId);
  if (chain.length < 2) return "";

  const shown = ctx.model.submissionById.get(submissionId)!;
  const currentId = ctx.model.currentVersion(submissionId);
  const current = ctx.model.submissionById.get(currentId);
  const currentTitle = current?.output?.manifest.title;
  const currentLabel = `<span class="submission-meta-id">${esc(currentId)}</span>${
    currentTitle ? ` ${ctx.markdown.renderAuthorInline(currentTitle, rootRel)}` : ""
  }`;
  const currentLink = `<a href="${attr(versionHref(rootRel, currentId))}">${currentLabel}</a>`;
  const draftProposal = shown.record.state === "draft" && ctx.model.supersedesClaim.has(submissionId);
  const superseded = !draftProposal && currentId !== submissionId;
  const compactCurrent = !draftProposal && !superseded;
  if (compactCurrent && !includeCurrentDialog) return "";
  const olderCount = chain.indexOf(submissionId);
  const countLabel = `${chain.length} ${chain.length === 1 ? "version" : "versions"}`;
  const summary = draftProposal
    ? `<strong>Proposed new version.</strong> This draft would follow the current registered version, ${currentLink}.`
    : superseded
      ? `<strong>Outdated version.</strong> You are viewing <span class="submission-meta-id">${esc(submissionId)}</span>. The current version is ${currentLink}.`
      : `<strong>Current version.</strong> ${olderCount} older ${olderCount === 1 ? "version is" : "versions are"} available for reference.`;
  const currentAction = currentId !== submissionId
    ? `<a class="version-current-button" href="${attr(versionHref(rootRel, currentId))}">Open current version <span aria-hidden="true">→</span></a>`
    : "";

  const rows = [...chain].reverse().map((id) => {
    const entry = ctx.model.submissionById.get(id);
    if (!entry) return "";
    const here = id === submissionId;
    const isCurrent = id === currentId;
    const title = entry.output?.manifest.title;
    const source = entry.record.source;
    const sourceHref = source
      ? githubSource(source.repository, source.commit, source.folder)
      : undefined;
    const dates = [
      `<span><b>Created</b> <time datetime="${attr(entry.record.createdAt)}">${formatDate(entry.record.createdAt)}</time></span>`,
      ...(entry.record.registeredAt
        ? [`<span><b>Registered</b> <time datetime="${attr(entry.record.registeredAt)}">${formatDate(entry.record.registeredAt)}</time></span>`]
        : []),
    ];
    const pins = entry.output ? [
      `<span><b>Lean</b> <code>${esc(entry.output.manifest.leanVersion)}</code></span>`,
      `<span><b>mathlib</b> <code>${esc(entry.output.manifest.mathlibVersion)}</code></span>`,
    ] : [];
    const marks = [
      isCurrent ? `<span class="version-mark version-mark-latest">current version</span>` : "",
      here ? `<span class="version-mark version-mark-viewing">viewing</span>` : "",
      entry.record.state === "draft" ? `<span class="version-mark version-mark-draft">draft</span>` : "",
    ].filter(Boolean).join("");
    const open = here
      ? `<span class="version-viewing-label">Shown on this page</span>`
      : `<a class="version-open-link" href="${attr(versionHref(rootRel, id))}">Open version <span aria-hidden="true">→</span></a>`;
    const github = sourceHref
      ? `<a class="version-source-link" href="${attr(sourceHref)}">${GITHUB_MARK}<span>GitHub source</span></a>`
      : `<span class="version-source-missing">Source unavailable</span>`;
    return `<li class="version-item${here ? " version-selected" : ""}${isCurrent ? " version-latest" : ""}"${here ? ' aria-current="page"' : ""}>
<div class="version-item-heading"><span class="version-item-id">${esc(id)}</span><span class="version-item-marks">${marks}</span></div>
${title ? `<p class="version-item-title">${ctx.markdown.renderAuthorInline(title, rootRel)}</p>` : ""}
<div class="version-metadata">${[...dates, ...pins].join("")}</div>
<div class="version-item-actions">${github}${open}</div>
</li>`;
  });

  const notice = compactCurrent ? "" : `<aside class="version-notice${superseded ? " version-notice-superseded" : ""}${draftProposal ? " version-notice-proposed" : ""}" aria-label="Submission version">
<p>${summary}</p>
<div class="version-notice-actions">${currentAction}<button class="version-history-button" type="button" data-version-dialog-open aria-haspopup="dialog" aria-controls="version-history-dialog">View ${countLabel}</button></div>
</aside>`;
  return `${notice}
<dialog class="version-history-dialog" id="version-history-dialog" data-version-dialog aria-labelledby="version-history-title">
<div class="version-dialog-header"><div><p class="version-dialog-eyebrow">Version history</p><h2 id="version-history-title">Submission versions</h2></div><button class="version-dialog-close" type="button" data-version-dialog-close aria-label="Close version history">×</button></div>
<p class="version-dialog-intro">Newest first. “Current version” is the latest registered successor; drafts are identified separately.</p>
<ol class="version-list">
${rows.join("\n")}
</ol>
</dialog>`;
}

/** Compact trigger appended to the technical metadata on the current
 * submission page. Superseded and proposed versions use the prominent notice
 * instead. */
export function versionHistoryMetaButton(ctx: PageContext, submissionId: string): string {
  const chain = ctx.model.versionHistory(submissionId);
  if (chain.length < 2 || ctx.model.currentVersion(submissionId) !== submissionId) return "";
  return `<button class="paper-version-button" type="button" data-version-dialog-open aria-haspopup="dialog" aria-controls="version-history-dialog">${chain.length} versions</button>`;
}

/** The submission page's paper-style masthead: big title and a compact
 * metadata line (id, authors, state, dates, source, pins). Falls back
 * gracefully when there is no build output yet (title = id). */
export function paperHeader(markdown: MarkdownRenderer, submission: SiteSubmission, rootRel: string, metaAction = ""): string {
  const { record, output } = submission;
  const title = output?.manifest.title ?? record.id;
  return `<header class="paper-head">
<h1 class="paper-title">${markdown.renderAuthorInline(title, rootRel)}</h1>
<p class="paper-meta">${metaBits(submission, metaAction)}</p>
</header>`;
}

/** The abstract, presented like a paper's: centered label, narrow measure. */
export function paperAbstract(rendered: string): string {
  return `<section class="paper-abstract">
<h2 class="abstract-heading">Abstract</h2>
<div class="latex-content">${rendered}</div>
</section>`;
}

/** Named authors (with ORCID/GitHub). An empty list intentionally omits the byline. */
function authorByline(submission: SiteSubmission): string {
  const authors = (submission.output?.manifest.authors ?? []).map((author) => {
    const name = author.orcid
      ? `<a class="paper-author-name" href="https://orcid.org/${attr(author.orcid)}" target="_blank" rel="noopener noreferrer">${esc(author.name)}</a>`
      : esc(author.name);
    const links = [
      author.github ? `<a href="https://github.com/${attr(author.github)}">@${esc(author.github)}</a>` : "",
    ].filter(Boolean).join(" ");
    return `<span class="paper-author">${name}${links ? ` <span class="author-links">${links}</span>` : ""}</span>`;
  });
  return authors.join('<span class="author-sep">·</span>');
}

/** The dim technical line under the title: id, authors, state, dates, source, pins. */
function metaBits(submission: SiteSubmission, metaAction: string): string {
  const { record, output } = submission;
  const source = record.source;
  const sourceBit = source
    ? (() => {
        const href = githubSource(source.repository, source.commit, source.folder);
        const short = `GitHub @${source.commit.slice(0, 7)}`;
        return href
          ? `<a href="${attr(href)}" title="${attr(href)}"><code>${esc(short)}</code></a>`
          : `<code>${esc(short)}</code>`;
      })()
    : "";
  const authors = authorByline(submission);
  const authorBit = authors
    ? `<span class="formalized-label">formalized by</span> ${authors}`
    : "";
  const dates = [
    `created ${formatDay(record.createdAt)}`,
    ...(record.registeredAt ? [`registered ${formatDay(record.registeredAt)}`] : []),
  ].join(" · ");
  const pins = output
    ? `Lean ${code(output.manifest.leanVersion)} · mathlib ${code(output.manifest.mathlibVersion.slice(0, 12))}`
    : "";
  // Drafts use the prominent page banner; repeating a tiny state pill here
  // makes the mutable state look like ordinary metadata.
  const state = record.state === "draft" ? "" : statePill(record.state);
  const id = output ? `<span class="submission-meta-id">${esc(record.id)}</span>` : "";
  const parts = [id, authorBit, state, dates, sourceBit, pins, metaAction].filter(Boolean);
  return parts.join('<span class="meta-sep">·</span>');
}

function formatDay(value: string): string {
  const date = new Date(value);
  return Number.isNaN(date.valueOf()) ? esc(value) : date.toISOString().slice(0, 10);
}

/** The copyable citation: all states are citable, drafts marked as such and
 * superseded versions naming the current registered successor. */
export function bibtex(model: SiteModel, submission: SiteSubmission): string {
  const { record, output } = submission;
  const manifest = output!.manifest;
  const clean = (s: string) => s.replace(/[{}\\]/g, "");
  const year = new Date(record.registeredAt ?? record.createdAt).getUTCFullYear();
  const author = manifest.authors.map((a) => clean(a.name)).join(" and ");
  const successor = model.isSuperseded(record.id) ? model.latestVersion(record.id) : undefined;
  const lines = [
    `@misc{${record.id},`,
    ...(author ? [`  author = {${author}},`] : []),
    `  title = {${clean(manifest.title)}},`,
    `  year = {${year}},`,
    `  howpublished = {Lax Archive, ${record.id}},`,
    `  url = {${DEFAULT_SITE_URL.replace(/\/+$/, "")}/${record.id}/},`,
    ...(record.state === "draft" ? ["  note = {draft},"] : []),
    ...(successor ? [`  note = {superseded by ${successor}},`] : []),
    `}`,
  ];
  return lines.join("\n");
}
