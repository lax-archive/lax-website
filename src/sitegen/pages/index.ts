import { attr, esc, formatDate, page, plural, statePill } from "../html.js";
import { contentMarkdown } from "../content.js";
import { indexSidebar, type PageContext } from "./shared.js";

/** The landing page: content/landing.md, then the submissions
 * library with its stats. Records that only reserved an id have nothing to
 * show and stay off the library and the stats (their pages exist for direct
 * links). */
export function indexPage({ model, markdown }: PageContext): string {
  const concepts = model.outputs.flatMap((o) => o.concepts);
  const statements = concepts.flatMap((c) => c.statements);
  const listed = model.submissions.filter((s) => s.output);
  const rows = listed.map((submission) => {
    const { record, output } = submission;
    const date = formatDate(record.registeredAt ?? record.createdAt);
    const authors = output!.manifest.authors.map((a) => esc(a.name)).join(", ");
    const counts = `${plural(output!.concepts.length, "concept")}, ${plural(output!.proofs.length, "proof")}`;
    return `<li><a class="submissions-list-link" href="${attr(record.id)}/index.html">
<span class="submissions-list-title"><span class="submission-title-id">${esc(record.id)}</span><span class="submission-title-inline-separator" aria-hidden="true">|</span>${esc(output!.manifest.title)}<span class="submissions-list-date">(${date})</span></span>
${authors ? `<span class="submissions-list-meta"><span class="formalized-label">formalized by</span> ${authors}</span>` : ""}
<span class="submissions-list-counts">${counts} ${statePill(record.state)}</span>
</a></li>`;
  });
  // The masthead follows the submission pages' paper grammar; the first
  // paragraph of landing.md is the lede, the rest the body.
  const text = contentMarkdown("landing.md").trim();
  const cut = text.indexOf("\n\n");
  const lede = cut === -1 ? text : text.slice(0, cut);
  const body = cut === -1 ? "" : text.slice(cut);
  const content = `<header class="paper-head landing-head">
<h1 class="paper-title">Lax <span class="site-title-quiet">Lean Archive</span></h1>
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
<ul class="submissions-list">
${rows.join("\n")}
</ul>
</div>`;
  return page({ title: "Lax Lean Archive", rootRel: "", sidebar: indexSidebar(model), content });
}
