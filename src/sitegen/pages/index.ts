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
const LAYERS_HEADING = "\n## How Lax works\n";
const PAPER_HEADING = "\n## The paper in brief\n";

function landingCopy(source: string): {
  kicker: string;
  lede: string;
  layers: string;
  paper: string;
  actions: Map<string, LandingAction>;
  submit: string;
} {
  const actionStart = source.indexOf(ACTION_HEADING);
  const submitStart = source.indexOf(SUBMIT_HEADING, actionStart + ACTION_HEADING.length);
  const layersStart = source.indexOf(LAYERS_HEADING);
  const paperStart = source.indexOf(PAPER_HEADING, layersStart + LAYERS_HEADING.length);
  if (layersStart === -1 || paperStart === -1 || actionStart === -1 || submitStart === -1)
    throw new Error("landing.md must contain the layers, paper, action, and submission headings");
  if (!(layersStart < paperStart && paperStart < actionStart && actionStart < submitStart))
    throw new Error("landing.md sections are out of order");

  const hero = source.slice(0, layersStart).trim();
  const kickerEnd = hero.indexOf("\n\n");
  const kicker = kickerEnd === -1 ? hero : hero.slice(0, kickerEnd);
  const lede = kickerEnd === -1 ? "" : hero.slice(kickerEnd).trim();
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
    kicker,
    lede,
    layers: source.slice(layersStart + LAYERS_HEADING.length, paperStart).trim(),
    paper: source.slice(paperStart + PAPER_HEADING.length, actionStart).trim(),
    actions,
    submit: source.slice(submitStart + SUBMIT_HEADING.length).trim(),
  };
}

function actionCard(action: LandingAction, available: boolean): string {
  const heading = `<span class="landing-action-title">${esc(action.title)}.</span>`;
  const copy = `<span class="landing-action-copy">${esc(action.description)}</span>`;
  if (!available) return `<div class="landing-action-card unavailable" id="landing-action-${attr(action.id)}" data-landing-view="${attr(action.id)}" role="button" aria-disabled="true" tabindex="0" aria-label="${attr(action.title)}, coming soon">
${heading}${copy}
<span class="landing-action-status" aria-hidden="true">Coming soon</span>
</div>`;
  return `<button class="landing-action-card" id="landing-action-${attr(action.id)}" type="button" data-landing-view="${attr(action.id)}" data-landing-action="${attr(action.id)}" aria-controls="landing-panel-${attr(action.id)}">
${heading}${copy}
<span class="landing-action-hint" aria-hidden="true">Go to section <b>↓</b></span>
</button>`;
}

function copyablePrompt(html: string): string {
  const open = "<pre>";
  const close = "</pre>";
  const start = html.indexOf(open);
  const end = html.indexOf(close, start + open.length);
  if (start < 0 || end < 0) throw new Error("landing submit section must include a fenced prompt");
  const prompt = html.slice(start, end + close.length)
    .replace(open, '<pre id="landing-submission-prompt">');
  return `${html.slice(0, start)}<div class="landing-prompt-box">
${prompt}
<button class="prompt-copy" type="button" data-copy-prompt aria-controls="landing-submission-prompt" aria-label="Copy prompt to clipboard" title="Copy prompt"><span class="prompt-copy-icon" aria-hidden="true"></span></button>
<output class="prompt-copy-status" aria-live="polite"></output>
</div>${html.slice(end + close.length)}`;
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
<span class="submissions-list-title"><span class="submission-title-id">${esc(record.id)}</span><span class="submission-title-inline-separator" aria-hidden="true">|</span>${markdown.renderAuthorInline(output!.manifest.title, "")}<span class="submissions-list-date">(${date})</span></span>
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
<strong>${markdown.renderAuthorInline(citeExample.output!.manifest.title, "")}</strong>
<span class="landing-cite-example-action">View citation <b aria-hidden="true">→</b></span>
</a>
</div>` : "";
  const library = `<section class="landing-action-panel submissions-library" id="landing-panel-read" aria-labelledby="landing-action-read">
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
  const submit = `<section class="landing-action-panel landing-submit-panel latex-content" id="landing-panel-submit" aria-labelledby="landing-action-submit">
<p class="landing-action-eyebrow">Contribute to Lax</p>
<h3>Creating your own submission</h3>
${copyablePrompt(markdown.render(landing.submit, ""))}
</section>`;
  const cite = `<section class="landing-action-panel landing-cite-panel" id="landing-panel-cite" aria-labelledby="landing-action-cite">
<p class="landing-action-eyebrow">Cite the formalization</p>
<h3>Ready-made BibTeX</h3>
<p>Every submission page ends with a <strong>Citation</strong> section containing a ready-made BibTeX entry. Open the submission you used, scroll to the bottom, and copy that entry into your bibliography.</p>
${citeExampleLink}
</section>`;
  const content = `<header class="landing-hero">
<div class="landing-hero-copy">
<p class="landing-kicker">${esc(landing.kicker)}</p>
<p class="landing-hero-title">Mathematics that can be read, checked, and built upon.</p>
<div class="landing-lede latex-content">
${markdown.render(landing.lede, "")}
</div>
<div class="landing-hero-actions">
<button class="landing-hero-button primary" type="button" data-landing-action="read" aria-controls="landing-panel-read">Browse submissions <b aria-hidden="true">↓</b></button>
<button class="landing-hero-button secondary" type="button" data-open-paper aria-expanded="false" aria-controls="landing-paper">The paper in two minutes <b aria-hidden="true">+</b></button>
</div>
</div>
<div class="landing-trust-path" aria-label="Concepts carry human-reviewed meaning; proofs provide machine-checked evidence.">
<div class="landing-trust-node concept">
<span class="landing-trust-step">01 · Concept</span>
<strong>Meaning</strong>
<small>read by people</small>
</div>
<span class="landing-trust-arrow" aria-hidden="true">→</span>
<div class="landing-trust-node proof">
<span class="landing-trust-step">02 · Proof</span>
<strong>Evidence</strong>
<small>checked by Lean</small>
</div>
</div>
</header>
<div class="landing-about">
<section class="landing-foundation" aria-labelledby="landing-foundation-heading">
<div class="landing-section-heading">
<p class="landing-section-eyebrow">Human meaning · machine certainty</p>
<h2 id="landing-foundation-heading">One submission, two layers</h2>
</div>
<div class="landing-layers latex-content">
${markdown.render(landing.layers, "")}
</div>
</section>
<details class="landing-paper" id="landing-paper">
<summary>
<span class="landing-paper-heading">
<span class="landing-section-eyebrow">From the white paper</span>
<span class="landing-paper-title">Why Lax, and why trust it?</span>
</span>
<span class="landing-paper-toggle" aria-hidden="true"><span class="when-closed">Expand</span><span class="when-open">Close</span><b></b></span>
</summary>
<div class="landing-paper-body latex-content">
${markdown.render(landing.paper, "")}
</div>
</details>
</div>
<section class="landing-actions" aria-labelledby="landing-actions-heading">
<h2 id="landing-actions-heading">What you can do here</h2>
<div class="landing-action-grid">
${actionCards.join("\n")}
</div>
<div class="landing-action-panels" aria-live="polite">
${submit}
${library}
${cite}
</div>
</section>`;
  return page({
    title: "Lax Lean Archive",
    rootRel: "",
    sidebar: indexSidebar(model, markdown),
    content,
    scripts: ["assets/landing.js"],
  });
}
