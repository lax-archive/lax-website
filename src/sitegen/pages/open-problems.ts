import type { StatementEntry } from "../../types.js";
import { attr, esc, page, plural, statePill, typeBadge } from "../html.js";
import { compareIds, type LocatedConcept, type SiteModel } from "../model.js";
import { shortId, type PageContext } from "./shared.js";

export interface OpenProblem {
  located: LocatedConcept;
  openStatements: StatementEntry[];
}

/** Claim-concepts with at least one statement outside the proof network's
 * least fixed point. Definitions have no statements and therefore stay out. */
export function collectOpenProblems(model: SiteModel): OpenProblem[] {
  return [...model.conceptHome.values()]
    .filter((located) => !model.isSuperseded(located.output.id))
    .map((located) => ({
      located,
      openStatements: located.concept.statements.filter((statement) =>
        !model.network.proven.has(statement.id)),
    }))
    .filter((problem) => problem.openStatements.length > 0)
    .sort((a, b) => compareIds(a.located.output.id, b.located.output.id)
      || a.located.concept.id.localeCompare(b.located.concept.id));
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
  const { output, concept } = problem.located;
  const href = `${output.id}/${concept.id}.html#s-${statement.id}`;
  const name = shortId(statement.id, concept.id);
  const explanation = statement.doc?.trim() || concept.description.trim();
  return `<li>
<p class="open-statement-name"><a href="${attr(href)}" title="${attr(statement.id)}"><code>${esc(name)}</code></a></p>
${explanation ? `<div class="open-statement-summary latex-content">${ctx.markdown.renderAuthorProse(explanation, "")}</div>` : ""}
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
  return `<li class="open-problem-card" data-type="${attr(type)}" data-search="${attr(searchText(problem))}">
<div class="open-problem-heading">
<div class="open-problem-title-line">${typeBadge(concept.type, false)}<h2><a href="${attr(href)}">${ctx.markdown.renderAuthorInline(concept.title, "")}</a></h2></div>
<p class="open-problem-meta"><a href="${attr(`${output.id}/index.html`)}"><code>${esc(output.id)}</code></a><span aria-hidden="true">·</span>${ctx.markdown.renderAuthorInline(output.manifest.title, "")}<span aria-hidden="true">·</span>${statePill(submission.record.state)}</p>
</div>
<p class="open-problem-count">${count}</p>
<ul class="open-statement-list">
${problem.openStatements.map((statement) => statementRow(ctx, problem, statement)).join("\n")}
</ul>
<p class="open-problem-action"><a href="${attr(href)}">Read the full concept <span aria-hidden="true">→</span></a></p>
</li>`;
}

/** Archive-wide index of proof obligations that are not yet grounded. */
export function openProblemsPage(ctx: PageContext): string {
  const problems = collectOpenProblems(ctx.model);
  const statementCount = problems.reduce((sum, problem) => sum + problem.openStatements.length, 0);
  const submissionCount = new Set(problems.map(({ located }) => located.output.id)).size;
  const content = `<header class="paper-head open-problems-head">
<h1 class="paper-title">Open Proof Obligations</h1>
<p class="paper-meta">${plural(problems.length, "proof obligation")} · ${plural(statementCount, "open statement")} · ${plural(submissionCount, "submission")}</p>
</header>
<div class="open-problems-intro latex-content">
<p>These proof obligations have at least one statement that is not yet supported by a grounded chain of archived proofs. Status is computed across the whole archive; draft submissions are included.</p>
</div>
${problems.length ? `<ul class="open-problems-list" id="open-problems-list">
${problems.map((problem) => problemRow(ctx, problem)).join("\n")}
<li id="open-problems-list-empty" class="open-problems-empty" hidden>No proof obligations match.</li>
</ul>` : `<p class="open-problems-empty">There are currently no open proof obligations; every claim in the archive has a grounded proof.</p>`}`;
  return page({
    title: "Open Proof Obligations — Lax Lean Archive",
    rootRel: "",
    sidebar: problemSidebar(problems, ctx),
    content,
  });
}
