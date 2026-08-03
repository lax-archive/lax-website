import { attr, esc, formatDate, page, plural, statePill } from "../html.js";
import { contentMarkdown } from "../content.js";
import {
  compareSearchSubmissions,
  indexSidebar,
  submissionSearchAttributes,
  type PageContext,
} from "./shared.js";

/** The landing page: content/landing.md, then the submissions
 * library with its stats. Records that only reserved an id have nothing to
 * show and stay off the library and the stats (their pages exist for direct
 * links). */
export function indexPage({ model, markdown }: PageContext): string {
  const concepts = model.outputs.flatMap((o) => o.concepts);
  const statements = concepts.flatMap((c) => c.statements);
  const listed = model.submissions.filter((s) => s.output).sort(compareSearchSubmissions);
  const rows = listed.map((submission, order) => {
    const { record, output } = submission;
    const date = formatDate(record.registeredAt ?? record.createdAt);
    const authors = output!.manifest.authors.map((a) => esc(a.name)).join(", ");
    const counts = `${plural(output!.concepts.length, "concept")}, ${plural(output!.proofs.length, "proof")}`;
    return `<li ${submissionSearchAttributes(submission, order)}><a class="submissions-list-link" href="${attr(record.id)}/index.html">
<span class="submissions-list-title"><span class="submission-title-id">${esc(record.id)}</span><span class="submission-title-inline-separator" aria-hidden="true">|</span>${esc(output!.manifest.title)}<span class="submissions-list-date">(${date})</span></span>
${authors ? `<span class="submissions-list-meta"><span class="formalized-label">formalized by</span> ${authors}</span>` : ""}
<span class="submissions-list-counts">${counts} ${statePill(record.state)}</span>
</a></li>`;
  });
  // The site header already names the archive, so the landing masthead only
  // carries landing.md's first paragraph as its lede; the rest is the body.
  const text = contentMarkdown("landing.md").trim();
  const cut = text.indexOf("\n\n");
  const lede = cut === -1 ? text : text.slice(0, cut);
  const body = cut === -1 ? "" : text.slice(cut);
  const content = `<header class="paper-head landing-head">
<div class="landing-lede latex-content">
${markdown.render(lede, "")}
</div>
</header>
<div class="landing-about latex-content">
${markdown.render(body, "")}
</div>
<div class="submissions-library">
<h2>Submissions</h2>
<p class="stats-line">${plural(listed.length, "submission")} · ${plural(concepts.length, "concept")} · ${plural(statements.length, "statement")}, ${model.network.proven.size} proven</p>
<ul class="submissions-list" id="submissions-list">
${rows.join("\n")}
<li id="submissions-list-empty" class="submissions-list-empty" hidden>No submissions match.</li>
</ul>
</div>`;
  return page({ title: "Lax Lean Archive", rootRel: "", sidebar: indexSidebar(model), content });
}
