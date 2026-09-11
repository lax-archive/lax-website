import type { StatementEntry } from "../../types.js";
import { attr, esc, page, plural, statePill, typeBadge } from "../html.js";
import { compareIds, type LocatedConcept, type SiteModel } from "../model.js";
import { INTRO_SUBMISSION_ID, type PageContext } from "./shared.js";

export interface OpenProblem {
  located: LocatedConcept;
  openStatements: StatementEntry[];
}

/** Editorial priority for the public list: explicit open questions first,
 * followed by registered theorems, registered lemmas, and draft results. */
function openProblemRank(problem: OpenProblem): number {
  const { submission, concept } = problem.located;
  const type = concept.type!.trim().toLowerCase();
  if (type === "open question") return 0;
  if (submission.record.state === "registered") return type === "theorem" ? 1 : 2;
  return 3;
}

/** Explicit open questions and theorem concepts from draft or registered
 * submissions, plus lemma concepts from registered submissions, with at least
 * one statement outside the proof network's least fixed point. */
export function collectOpenProblems(model: SiteModel): OpenProblem[] {
  const candidates = [...model.conceptHome.values()]
    .filter(({ submission, output, concept }) => {
      if (output.id === INTRO_SUBMISSION_ID) return false;
      if (model.isSuperseded(output.id)) return false;
      const type = concept.type!.trim().toLowerCase();
      const state = submission.record.state;
      if (state !== "draft" && state !== "registered") return false;
      return type === "open question" || type === "theorem"
        || (state === "registered" && type === "lemma");
    })
    .map((located) => ({
      located,
      openStatements: located.concept.statements.filter((statement) =>
        !model.network.proven.has(statement.id)),
    }))
    .filter((problem) => problem.openStatements.length > 0)
    .sort((a, b) => openProblemRank(a) - openProblemRank(b)
      || compareIds(a.located.output.id, b.located.output.id)
      || a.located.concept.id.localeCompare(b.located.concept.id));

  // Work in progress is useful context, but it should not overwhelm the
  // archive-wide view. Keep the highest-priority statement from each
  // non-registered submission after applying the editorial sort above.
  const seenNonRegistered = new Set<string>();
  return candidates.flatMap((problem) => {
    if (problem.located.submission.record.state === "registered") return [problem];
    const submissionId = problem.located.output.id;
    if (seenNonRegistered.has(submissionId)) return [];
    seenNonRegistered.add(submissionId);
    return [{ ...problem, openStatements: problem.openStatements.slice(0, 1) }];
  });
}

function searchText(problem: OpenProblem): string {
  const { submission, output, concept } = problem.located;
  return [
    concept.id,
    concept.title,
    concept.type,
    output.id,
    output.manifest.title,
    submission.record.state,
    ...problem.openStatements.flatMap((statement) => [statement.id, statement.doc ?? ""]),
  ].join(" ").replace(/\s+/g, " ").trim().toLowerCase();
}

function problemSidebar(problems: OpenProblem[], ctx: PageContext): string {
  const types = [...new Set(problems.map(({ located }) =>
    located.concept.type!.trim().toLowerCase()))].sort();
  const typeOptions = types
    .map((type) => `<option value="${attr(type)}">${esc(type)}</option>`)
    .join("\n");
  const rows = problems.map((problem) => {
    const { output, concept } = problem.located;
    const type = concept.type!.trim().toLowerCase();
    const href = `${output.id}/${concept.id}.html`;
    return `<li data-type="${attr(type)}" data-search="${attr(searchText(problem))}"><a class="entry-link" href="${attr(href)}" data-full-title="${attr(concept.title)}"><span class="entry-label">${typeBadge(concept.type, false)}<span class="entry-label-text">${ctx.markdown.renderAuthorInline(concept.title, "")}</span></span></a></li>`;
  });
  return `<a class="sidebar-back" href="index.html"><span class="sidebar-back-arrow" aria-hidden="true">←</span>Archive</a>
<div class="sidebar-filters"><div class="filter-group">
<label for="filter-search">Search</label>
<input id="filter-search" class="filter-input" type="search" placeholder="Search proof obligations" aria-controls="entry-list open-problems-list">
</div>
<div class="filter-group">
<label for="filter-type">Type</label>
<select id="filter-type" class="filter-select">
<option value="all">All types</option>
${typeOptions}
</select>
</div></div>
<ul id="entry-list">
${rows.join("\n")}
<li id="entry-list-empty" hidden>No proof obligations match.</li>
</ul>`;
}

function statementRow(ctx: PageContext, problem: OpenProblem, statement: StatementEntry): string {
  const { concept } = problem.located;
  const explanation = statement.doc?.trim() || concept.description.trim();
  if (!explanation) return "";
  return `<li>
<div class="open-statement-summary latex-content">${ctx.markdown.renderAuthorProse(explanation, "")}</div>
</li>`;
}

function problemRow(ctx: PageContext, problem: OpenProblem): string {
  const { submission, output, concept } = problem.located;
  const type = concept.type!.trim().toLowerCase();
  const href = `${output.id}/${concept.id}.html`;
  const allOpen = problem.openStatements.length === concept.statements.length;
  const count = allOpen
    ? plural(problem.openStatements.length, "open statement")
    : `${problem.openStatements.length} of ${concept.statements.length} statements open`;
  const statementRows = problem.openStatements
    .map((statement) => statementRow(ctx, problem, statement))
    .filter(Boolean)
    .join("\n");
  return `<li class="open-problem-card" data-type="${attr(type)}" data-search="${attr(searchText(problem))}">
<div class="open-problem-heading">
<div class="open-problem-title-line">${typeBadge(concept.type, false)}<h2><a href="${attr(href)}">${ctx.markdown.renderAuthorInline(concept.title, "")}</a></h2></div>
<p class="open-problem-meta"><a href="${attr(`${output.id}/index.html`)}"><code>${esc(output.id)}</code></a><span aria-hidden="true">·</span>${ctx.markdown.renderAuthorInline(output.manifest.title, "")}<span aria-hidden="true">·</span>${statePill(submission.record.state)}</p>
</div>
<p class="open-problem-count">${count}</p>
${statementRows ? `<ul class="open-statement-list">
${statementRows}
</ul>` : ""}
<p class="open-problem-action"><a href="${attr(href)}">Take a look at the concept <span aria-hidden="true">→</span></a></p>
</li>`;
}

/** Archive-wide index of eligible statements that are not yet grounded. */
export function openProblemsPage(ctx: PageContext): string {
  const problems = collectOpenProblems(ctx.model);
  const statementCount = problems.reduce((sum, problem) => sum + problem.openStatements.length, 0);
  const submissionCount = new Set(problems.map(({ located }) => located.output.id)).size;
  const content = `<header class="paper-head open-problems-head">
<h1 class="paper-title">Open Proof Obligations</h1>
<p class="paper-meta">${plural(problems.length, "proof obligation")} · ${plural(statementCount, "open statement")} · ${plural(submissionCount, "submission")}</p>
</header>
<div class="open-problems-intro latex-content">
<p>This page includes open questions and theorem statements from draft and registered submissions, plus lemma statements from registered submissions, when they are not yet supported by a grounded chain of archived proofs. To keep work in progress from crowding out registered results, at most one statement is shown from each non-registered submission.</p>
</div>
${problems.length ? `<ul class="open-problems-list" id="open-problems-list">
${problems.map((problem) => problemRow(ctx, problem)).join("\n")}
<li id="open-problems-list-empty" class="open-problems-empty" hidden>No proof obligations match.</li>
</ul>` : `<p class="open-problems-empty">There are currently no open proof obligations that qualify for this view.</p>`}`;
  return page({
    title: "Open Proof Obligations — Lax Lean Archive",
    rootRel: "",
    sidebar: problemSidebar(problems, ctx),
    content,
  });
}
