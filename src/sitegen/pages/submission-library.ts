import { attr, esc, formatDate, plural, statePill } from "../html.js";
import { submissionTagIndex } from "../tags.js";
import {
  anonymityPlaceholder,
  currentSubmissions,
  submissionSearchAttributes,
  type PageContext,
} from "./shared.js";

interface SubmissionLibraryOptions {
  /** Prefix from this page to the site root. */
  rootRel: string;
  /** Heading elsewhere on the page that names the library. */
  labelledBy: string;
  /** The landing page scroll target; the standalone page uses its own id. */
  id: string;
  standalone?: boolean;
}

/** The searchable, faceted submission library shared by the landing page and
 * `/submissions/`. Keeping one renderer makes their ordering and metadata
 * identical; only links and standalone layout differ. */
export function submissionLibrary(ctx: PageContext, options: SubmissionLibraryOptions): string {
  const { model, markdown } = ctx;
  const listed = currentSubmissions(model);
  const concepts = listed.flatMap((submission) => submission.output!.concepts);
  const statements = concepts.flatMap((concept) => concept.statements);
  const provenStatements = statements.filter((statement) => model.network.proven.has(statement.id)).length;
  const tagIndex = submissionTagIndex(listed);
  const rows = listed.map((submission, order) => {
    const { record, output } = submission;
    // The creation date is also what orders the list. Registration remains
    // available on the submission page itself.
    const date = formatDate(record.createdAt);
    const authors = output!.manifest.anonymous === true && output!.manifest.authors.length
      ? anonymityPlaceholder("withheld during anonymous review", "anonymity-placeholder-inline")
      : output!.manifest.authors.map((author) => esc(author.name)).join(", ");
    const counts = `${plural(output!.concepts.length, "concept")}, ${plural(output!.proofs.length, "proof")}`;
    return `<li ${submissionSearchAttributes(submission, order, tagIndex.bySubmission.get(record.id))}><a class="submissions-list-link" href="${attr(`${options.rootRel}${record.id}/index.html`)}">
<span class="submissions-list-title"><span class="submission-find-alias" hidden="until-found" aria-hidden="true" data-submission-find-alias>${esc(record.id)}</span>${markdown.renderAuthorInline(output!.manifest.title, options.rootRel)}<span class="submissions-list-date">(${date})</span></span>
${authors ? `<span class="submissions-list-meta"><span class="formalized-label">formalized by</span> ${authors}</span>` : ""}
<span class="submissions-list-counts">${counts} ${statePill(record.state)}</span>
</a></li>`;
  });

  const chip = (key: string, label: string, count: number, extraClass = ""): string =>
    `<button class="tag-chip${extraClass}" type="button" data-tag-filter="${attr(key)}" aria-pressed="false" aria-label="${attr(`${label}, ${plural(count, "submission")}`)}"><span>${esc(label)}</span><b aria-hidden="true">${count}</b></button>`;
  // Environments share the topic strip, but appear only when the archive
  // contains more than one environment.
  const environmentButtons = model.environments.length > 1
    ? model.environments.map((environment) => chip(
        environment,
        environment === model.epoch ? `${environment} · epoch` : environment,
        listed.filter((submission) => model.environmentOf.get(submission.record.id) === environment).length,
        " environment-chip",
      ))
    : [];
  const tagButtons = tagIndex.tags.map((tag) => chip(tag.key, tag.label, tag.submissionIds.length));
  const facetButtons = [...environmentButtons, ...tagButtons];
  const facetSummary = environmentButtons.length
    ? "Environments first, then topics suggested from submission and concept titles."
    : "Suggested from submission and concept titles.";
  const tagBrowser = facetButtons.length ? `<section class="tag-browser" aria-labelledby="tag-browser-heading">
<div class="tag-browser-heading"><h4 id="tag-browser-heading">Browse by topic</h4><p>${esc(facetSummary)}</p></div>
<div class="tag-chip-list" role="group" aria-label="Filter submissions by topic">
<button class="tag-chip" type="button" data-tag-filter="" aria-pressed="true" aria-label="All, ${plural(listed.length, "submission")}"><span>All</span><b aria-hidden="true">${listed.length}</b></button>
${facetButtons.join("\n")}
</div>
<p class="tag-results-status" id="tag-results-status" aria-live="polite">Showing all ${plural(listed.length, "submission")}.</p>
</section>` : "";

  const standalone = options.standalone ? " submissions-page-library" : "";
  return `<section class="landing-action-panel submissions-library${standalone}" id="${attr(options.id)}" aria-labelledby="${attr(options.labelledBy)}">
<div class="landing-action-panel-heading">
<p class="stats-line">${plural(listed.length, "submission")} · ${plural(concepts.length, "concept")} · ${plural(statements.length, "statement")}, ${provenStatements} proven</p>
<input id="submissions-search" class="filter-input submissions-library-search" type="search" placeholder="Search titles and concepts" aria-label="Search submissions" aria-controls="submissions-list">
</div>
${tagBrowser}
<ul class="submissions-list" id="submissions-list">
${rows.join("\n")}
<li id="submissions-list-empty" class="submissions-list-empty" hidden>No submissions match.</li>
</ul>
<button class="submissions-load-more" id="submissions-load-more" type="button" aria-controls="submissions-list" hidden>Load more <b aria-hidden="true">↓</b></button>
</section>`;
}
