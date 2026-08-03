import { attr, esc, formatDate, page, plural, statePill } from "../html.js";
import { contentMarkdown } from "../content.js";
import {
  compareSearchSubmissions,
  indexSidebar,
  submissionSearchAttributes,
  type PageContext,
} from "./shared.js";

interface LandingAction { id: string; title: string; description: string }

const ACTION_HEADING = "\n## What you can do here\n";
const SUBMIT_HEADING = "\n## Creating your own submission\n";

function landingCopy(source: string): {
  lede: string;
  introduction: string;
  actions: Map<string, LandingAction>;
  submit: string;
} {
  const actionStart = source.indexOf(ACTION_HEADING);
  const submitStart = source.indexOf(SUBMIT_HEADING, actionStart + ACTION_HEADING.length);
  if (actionStart === -1 || submitStart === -1)
    throw new Error("landing.md must contain the action and submission headings");

  const introduction = source.slice(0, actionStart).trim();
  const ledeEnd = introduction.indexOf("\n\n");
  const lede = ledeEnd === -1 ? introduction : introduction.slice(0, ledeEnd);
  const body = ledeEnd === -1 ? "" : introduction.slice(ledeEnd).trim();
  const actionSource = source.slice(actionStart + ACTION_HEADING.length, submitStart).trim();
  const actions = new Map<string, LandingAction>();
  for (const chunk of actionSource.split(/\n(?=- \*\*)/)) {
    const match = /^- \*\*([^*]+)\.\*\*\s+([\s\S]+)$/.exec(chunk.trim());
    if (!match) throw new Error(`invalid landing action: ${chunk}`);
    const title = match[1]!.trim();
    const id = title.toLowerCase();
    actions.set(id, { id, title, description: match[2]!.replace(/\s+/g, " ").trim() });
  }
  for (const id of ["read", "review", "submit", "cite"])
    if (!actions.has(id)) throw new Error(`landing.md is missing the ${id} action`);

  return {
    lede,
    introduction: body,
    actions,
    submit: source.slice(submitStart + SUBMIT_HEADING.length).trim(),
  };
}

function actionCard(action: LandingAction, available: boolean): string {
  const heading = `<span class="landing-action-title">${esc(action.title)}.</span>`;
  const copy = `<span class="landing-action-copy">${esc(action.description)}</span>`;
  if (!available) return `<div class="landing-action-card unavailable" tabindex="0" aria-label="${attr(action.title)}, coming soon">
${heading}${copy}
<span class="landing-action-status" aria-hidden="true">Coming soon</span>
</div>`;
  return `<button class="landing-action-card" id="landing-action-${attr(action.id)}" type="button" data-landing-action="${attr(action.id)}" aria-expanded="false" aria-controls="landing-panel-${attr(action.id)}">
${heading}${copy}
<span class="landing-action-hint" aria-hidden="true"><span class="when-closed">Open <b>↓</b></span><span class="when-open">Close <b>↑</b></span></span>
</button>`;
}

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
  const landing = landingCopy(contentMarkdown("landing.md").trim());
  const actionOrder = ["read", "review", "submit", "cite"];
  const actionCards = actionOrder.map((id) => actionCard(landing.actions.get(id)!, id !== "review"));
  const citeExample = listed.find((submission) => submission.record.id.toLowerCase().replace(/[^a-z0-9]/g, "") === "lax17")
    ?? listed.find((submission) => submission.record.state === "registered")
    ?? listed[0];
  const citeExampleLink = citeExample ? `<div class="landing-cite-example">
<p>Example submission</p>
<a href="${attr(citeExample.record.id)}/index.html#citation">
<span class="landing-cite-example-id">${esc(citeExample.record.id)}</span>
<strong>${esc(citeExample.output!.manifest.title)}</strong>
<span class="landing-cite-example-action">See its BibTeX <b aria-hidden="true">→</b></span>
</a>
</div>` : "";
  const library = `<section class="landing-action-panel submissions-library" id="landing-panel-read" aria-labelledby="landing-action-read" hidden>
<div class="landing-action-panel-heading">
<p class="landing-action-eyebrow">Read the archive</p>
<h3>Submissions</h3>
<p class="stats-line">${plural(listed.length, "submission")} · ${plural(concepts.length, "concept")} · ${plural(statements.length, "statement")}, ${model.network.proven.size} proven</p>
</div>
<ul class="submissions-list" id="submissions-list">
${rows.join("\n")}
<li id="submissions-list-empty" class="submissions-list-empty" hidden>No submissions match.</li>
</ul>
</section>`;
  const submit = `<section class="landing-action-panel landing-submit-panel latex-content" id="landing-panel-submit" aria-labelledby="landing-action-submit" hidden>
<p class="landing-action-eyebrow">Contribute to Lax</p>
<h3>Creating your own submission</h3>
${markdown.render(landing.submit, "")}
</section>`;
  const cite = `<section class="landing-action-panel landing-cite-panel" id="landing-panel-cite" aria-labelledby="landing-action-cite" hidden>
<p class="landing-action-eyebrow">Cite the formalization</p>
<h3>Ready-made BibTeX</h3>
<p>Every submission page ends with a <strong>Citation</strong> section containing a ready-made BibTeX entry. Open the submission you used, scroll to the bottom, and copy that entry into your bibliography.</p>
${citeExampleLink}
</section>`;
  const content = `<header class="paper-head landing-head">
<div class="landing-lede latex-content">
${markdown.render(landing.lede, "")}
</div>
</header>
<div class="landing-about latex-content">
${markdown.render(landing.introduction, "")}
</div>
<section class="landing-actions" aria-labelledby="landing-actions-heading">
<h2 id="landing-actions-heading">What you can do here</h2>
<div class="landing-action-grid">
${actionCards.join("\n")}
</div>
<div class="landing-action-panels" aria-live="polite">
${library}
${submit}
${cite}
</div>
</section>`;
  return page({
    title: "Lax Lean Archive",
    rootRel: "",
    sidebar: indexSidebar(model),
    content,
    scripts: ["assets/landing.js"],
  });
}
