import { attr, esc, formatDate, page, plural, statePill } from "../html.js";
import { contentMarkdown } from "../content.js";
import { highlightSnippet } from "../highlight.js";
import { submissionTagIndex } from "../tags.js";
import {
  bibtex,
  compareSearchSubmissions,
  indexSidebar,
  submissionSearchAttributes,
  type PageContext,
} from "./shared.js";
import { collectOpenProblems } from "./open-problems.js";

interface LandingAction { id: string; title: string; description: string }

const ACTION_HEADING = "\n## What you can do here\n";
const SUBMIT_HEADING = "\n## Creating your own submission\n";

const CONCEPT_DEMO = String.raw`import Mathlib.Combinatorics.SimpleGraph.Clique

open Filter Real SimpleGraph

abbrev C₅ : SimpleGraph (Fin 5) := cycleGraph 5

def C₅Free {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ¬ ∃ f : Fin 5 ↪ V, C₅ = G.comap f

def HasLargeHomogeneousSet {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℝ) : Prop :=
  G.indepNum ≥ r ∨ G.cliqueNum ≥ r

axiom erdosHajnal_C₅ :
  ∃ c > 0, ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    C₅Free G → HasLargeHomogeneousSet G ((n : ℝ) ^ c)`;

const PROOF_DEMO = String.raw`theorem erdosHajnal_C₅ :
    ∃ c > 0,
      ∀ᶠ n in atTop,
        ∀ G : SimpleGraph (Fin n),
          C₅Free G →
            HasLargeHomogeneousSet G ((n : ℝ) ^ c) := by
  obtain ⟨c, hc, hmain⟩ :=
    polynomial_homogeneous_set_for_five_hole
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmain] with n hn
  intro G hG
  exact hn G (by
    simpa [C₅Free] using hG)`;

function landingDemoFace(
  side: "concept" | "proof",
  path: string,
  code: string,
): string {
  const concept = side === "concept";
  const codeBlock = concept
    ? `<span class="landing-demo-code"><code>${code}</code></span>`
    : `<span class="landing-demo-code landing-demo-code-excerpt">
<span class="landing-demo-continuation" aria-hidden="true"><i></i><b>⋮</b><i></i></span>
<code>${code}</code>
<span class="landing-demo-continuation" aria-hidden="true"><i></i><b>⋮</b><i></i></span>
</span>`;
  return `<span class="landing-demo-face landing-demo-${side}" aria-hidden="true">
<span class="landing-demo-filebar">
<span class="landing-demo-file-heading"><strong>${concept ? "Concept file" : "Proof file"}</strong>${concept ? "" : '<span class="landing-demo-file-note">excerpt</span>'}</span>
<span class="landing-demo-file-path">${esc(path)}</span>
</span>
${codeBlock}
<span class="landing-demo-trust">
<span class="landing-demo-trust-copy"><strong>${concept ? "Meaning" : "Evidence"}</strong><small>${concept ? "read by people" : "checked by Lean"}</small></span>
${concept ? '<span class="landing-demo-turn"><span>See the proof</span><b>↻</b></span>' : ""}
</span>
</span>`;
}

async function landingDemo(): Promise<string> {
  const [concept, proof] = await Promise.all([
    highlightSnippet(CONCEPT_DEMO, { accentLines: [14, 15, 16] }),
    highlightSnippet(PROOF_DEMO, { startLine: 417 }),
  ]);
  return `<button class="landing-demo-card" type="button" data-proof-flip aria-pressed="false" aria-label="Concept file: Erdős–Hajnal for the five-cycle. Hover or activate to see a proof excerpt.">
<span class="landing-demo-inner">
${landingDemoFace("concept", "concepts/ErdosHajnal/C5.lean", concept)}
${landingDemoFace("proof", "proofs/ErdosHajnalProofs/C5.lean", proof)}
</span>
</button>`;
}

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
  if (actionStart >= submitStart)
    throw new Error("landing.md sections are out of order");

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
  // The agent prompt is the section's last fence; earlier fences (the setup
  // commands) stay plain code blocks.
  const open = "<pre>";
  const close = "</pre>";
  const start = html.lastIndexOf(open);
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
export async function indexPage({ model, markdown }: PageContext): Promise<string> {
  const concepts = model.outputs.flatMap((o) => o.concepts);
  const statements = concepts.flatMap((c) => c.statements);
  const listed = model.submissions.filter((s) => s.output).sort(compareSearchSubmissions);
  const tagIndex = submissionTagIndex(listed);
  const rows = listed.map((submission, order) => {
    const { record, output } = submission;
    const date = formatDate(record.registeredAt ?? record.createdAt);
    const authors = output!.manifest.authors.map((a) => esc(a.name)).join(", ");
    const counts = `${plural(output!.concepts.length, "concept")}, ${plural(output!.proofs.length, "proof")}`;
    return `<li ${submissionSearchAttributes(submission, order, tagIndex.bySubmission.get(record.id))}><a class="submissions-list-link" href="${attr(record.id)}/index.html">
<span class="submissions-list-title">${markdown.renderAuthorInline(output!.manifest.title, "")}<span class="submissions-list-date">(${date})</span></span>
${authors ? `<span class="submissions-list-meta"><span class="formalized-label">formalized by</span> ${authors}</span>` : ""}
<span class="submissions-list-counts">${counts} ${statePill(record.state)}</span>
</a></li>`;
  });
  const landing = landingCopy(contentMarkdown("landing.md").trim());
  const demo = await landingDemo();
  const actionOrder = ["read", "review", "submit", "cite"];
  const actionCards = actionOrder.map((id) => actionCard(landing.actions.get(id)!, true));
  const openProblems = collectOpenProblems(model);
  const openProblemSubmissions = new Set(openProblems.map(({ located }) => located.output.id)).size;
  const citeExample = listed.find((submission) => submission.record.id.toLowerCase().replace(/[^a-z0-9]/g, "") === "lax17")
    ?? listed.find((submission) => submission.record.state === "registered")
    ?? listed[0];
  const citeExampleLink = citeExample ? `<div class="landing-cite-example">
<p>Example submission</p>
<a href="${attr(citeExample.record.id)}/index.html#citation">
<span class="landing-cite-example-id">${esc(citeExample.record.id)}</span>
<pre class="landing-cite-example-bib">${esc(bibtex(citeExample))}</pre>
<span class="landing-cite-example-action">See in action <b aria-hidden="true">→</b></span>
</a>
</div>` : "";
  const tagButtons = tagIndex.tags.map((tag) => {
    const count = tag.submissionIds.length;
    return `<button class="tag-chip" type="button" data-tag-filter="${attr(tag.key)}" aria-pressed="false" aria-label="${attr(`${tag.label}, ${plural(count, "submission")}`)}"><span>${esc(tag.label)}</span><b aria-hidden="true">${count}</b></button>`;
  });
  const tagBrowser = tagButtons.length ? `<section class="tag-browser" aria-labelledby="tag-browser-heading">
<div class="tag-browser-heading"><h4 id="tag-browser-heading">Browse by topic</h4><p>Suggested from submission and concept titles.</p></div>
<div class="tag-chip-list" role="group" aria-label="Filter submissions by topic">
<button class="tag-chip" type="button" data-tag-filter="" aria-pressed="true" aria-label="All, ${plural(listed.length, "submission")}"><span>All</span><b aria-hidden="true">${listed.length}</b></button>
${tagButtons.join("\n")}
</div>
<p class="tag-results-status" id="tag-results-status" aria-live="polite">Showing all ${plural(listed.length, "submission")}.</p>
</section>` : "";
  const library = `<section class="landing-action-panel submissions-library" id="landing-panel-read" aria-labelledby="landing-action-read">
<div class="landing-action-panel-heading">
<p class="landing-action-eyebrow">Read the archive</p>
<h3>Submissions</h3>
<p class="stats-line">${plural(listed.length, "submission")} · ${plural(concepts.length, "concept")} · ${plural(statements.length, "statement")}, ${model.network.proven.size} proven</p>
</div>
${tagBrowser}
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
  const review = `<section class="landing-action-panel landing-review-panel" id="landing-panel-review" aria-labelledby="landing-action-review">
<p class="landing-action-eyebrow">Contribute a proof</p>
<h3>Open Proof Obligations</h3>
<p>${openProblems.length
    ? `Browse every claim that does not yet have a grounded proof, across ${plural(openProblemSubmissions, "submission")}.`
    : "Every claim currently has a grounded proof; this view will update automatically when a proof obligation is submitted."}</p>
<a class="landing-open-problems-link" href="open-proof-obligations.html"><span><strong>${openProblems.length}</strong> ${openProblems.length === 1 ? "proof obligation" : "proof obligations"}</span><b>Browse proof obligations <span aria-hidden="true">→</span></b></a>
</section>`;
  const cite = `<section class="landing-action-panel landing-cite-panel" id="landing-panel-cite" aria-labelledby="landing-action-cite">
<p class="landing-action-eyebrow">Cite the formalization</p>
<h3>Ready-made BibTeX</h3>
<p>Every submission page ends with a <strong>Citation</strong> section containing a ready-made BibTeX entry. Open the submission you used, scroll to the bottom, and copy that entry into your bibliography.</p>
${citeExampleLink}
</section>`;
  const content = `<section class="landing-demo-showcase" aria-label="How Lax separates mathematical meaning from proof evidence">
<div class="landing-lede latex-content">
${markdown.render(landing.lede, "")}
</div>
${demo}
<div class="landing-demo-summary latex-content">
${markdown.render(landing.introduction, "")}
</div>
<div class="landing-hero-actions">
<button class="landing-hero-button primary" type="button" data-landing-action="read" aria-controls="landing-panel-read">Browse submissions <b aria-hidden="true">↓</b></button>
<a class="landing-hero-button secondary" href="assets/lax-white-paper.pdf" download="lax-white-paper.pdf">Read the Lax paper <b aria-hidden="true">↗</b></a>
</div>
</section>
<section class="landing-actions" aria-labelledby="landing-actions-heading">
<h2 id="landing-actions-heading">What you can do here</h2>
<div class="landing-action-grid">
${actionCards.join("\n")}
</div>
<div class="landing-action-panels" aria-live="polite">
${submit}
${library}
${review}
${cite}
</div>
</section>`;
  return page({
    title: "Lax Lean Archive",
    rootRel: "",
    sidebar: indexSidebar(model, markdown, tagIndex.bySubmission),
    content,
    scripts: ["assets/landing.js"],
  });
}
