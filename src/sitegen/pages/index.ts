import { attr, esc, formatDate, page, plural, statePill } from "../html.js";
import { contentMarkdown } from "../content.js";
import { highlightSnippet } from "../highlight.js";
import { submissionTagIndex } from "../tags.js";
import {
  currentSubmissions,
  indexSidebar,
  submissionSearchAttributes,
  type PageContext,
} from "./shared.js";
import { collectOpenProblems } from "./open-problems.js";

interface LandingAction { id: string; title: string; description: string }
interface LandingFaq { question: string; answer: string }

const ACTION_HEADING = "\n## What you can do here\n";
const SUBMIT_HEADING = "\n## Creating your own submission\n";
const REVIEW_OTHER_SUBMISSION_WEIGHT = 10;

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

function landingFaqCopy(source: string): {
  title: string;
  items: LandingFaq[];
} {
  const chunks = source.trim().split(/\n(?=## )/);
  const heading = /^# ([^\n]+)$/.exec((chunks.shift() ?? "").trim());
  if (!heading) throw new Error("faq.md must start with a title");

  const items = chunks.map((chunk) => {
    const match = /^## ([^\n]+)\n+([\s\S]+)$/.exec(chunk.trim());
    if (!match) throw new Error(`invalid FAQ entry: ${chunk}`);
    return { question: match[1]!.trim(), answer: match[2]!.trim() };
  });
  if (!items.length) throw new Error("faq.md must contain at least one question");

  return {
    title: heading[1]!.trim(),
    items,
  };
}

function landingFaq(source: string, markdown: PageContext["markdown"]): string {
  const faq = landingFaqCopy(source);
  const items = faq.items.map(({ question, answer }, index) => `<li class="landing-faq-list-item"><details class="landing-faq-item">
<summary><span class="landing-faq-question"><span class="landing-faq-number" aria-hidden="true">${String(index + 1).padStart(2, "0")}</span><span>${esc(question)}</span></span><span class="landing-faq-toggle" aria-hidden="true"></span></summary>
<div class="landing-faq-answer latex-content">
${markdown.render(answer, "")}
</div>
</details></li>`).join("\n");

  return `<section class="landing-faq" id="faq" aria-labelledby="landing-faq-heading">
<header class="landing-faq-heading">
<p class="landing-action-eyebrow">About Lax</p>
<h2 id="landing-faq-heading">${esc(faq.title)}</h2>
</header>
<ol class="landing-faq-list">
${items}
</ol>
</section>`;
}

function actionCard(action: LandingAction, available: boolean, href?: string): string {
  const heading = `<span class="landing-action-title">${esc(action.title)}.</span>`;
  const copy = `<span class="landing-action-copy">${esc(action.description)}</span>`;
  if (!available) return `<div class="landing-action-card unavailable" id="landing-action-${attr(action.id)}" data-landing-view="${attr(action.id)}" role="button" aria-disabled="true" tabindex="0" aria-label="${attr(action.title)}, coming soon">
${heading}${copy}
<span class="landing-action-status" aria-hidden="true">Coming soon</span>
</div>`;
  if (href) return `<a class="landing-action-card" id="landing-action-${attr(action.id)}" href="${attr(href)}" data-landing-view="${attr(action.id)}">
${heading}${copy}
<span class="landing-action-hint" aria-hidden="true">See citation <b>→</b></span>
</a>`;
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
  const listed = currentSubmissions(model);
  const currentIds = new Set(listed.map((submission) => submission.record.id));
  const concepts = listed.flatMap((submission) => submission.output!.concepts);
  const statements = concepts.flatMap((c) => c.statements);
  const provenStatements = statements.filter((statement) => model.network.proven.has(statement.id)).length;
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
  const faq = landingFaq(contentMarkdown("faq.md"), markdown);
  const demo = await landingDemo();
  const actionOrder = ["read", "review", "submit", "cite"];
  const reviewConcepts = concepts
    .map((concept) => {
      const located = model.conceptHome.get(concept.id)!;
      const users = [...new Map(
        (model.importers.get(concept.id) ?? [])
          .filter((user) => user.concept.id !== concept.id && currentIds.has(user.output.id))
          .map((user) => [user.concept.id, user]),
      ).values()];
      const otherSubmissionCount = new Set(
        users
          .filter((user) => user.output.id !== located.output.id)
          .map((user) => user.output.id),
      ).size;
      return {
        located,
        users,
        otherSubmissionCount,
        weight: otherSubmissionCount * REVIEW_OTHER_SUBMISSION_WEIGHT + users.length,
      };
    })
    .filter(({ otherSubmissionCount }) => otherSubmissionCount > 0)
    .sort((a, b) =>
      Number(b.located.submission.record.state === "registered") - Number(a.located.submission.record.state === "registered")
      || b.weight - a.weight
      || a.located.concept.id.localeCompare(b.located.concept.id))
    .slice(0, 8);
  const openProblems = collectOpenProblems(model);
  const openProblemSubmissions = new Set(openProblems.map(({ located }) => located.output.id)).size;
  const citeExample = listed.find((submission) => submission.record.id.toLowerCase().replace(/[^a-z0-9]/g, "") === "lax17")
    ?? listed.find((submission) => submission.record.state === "registered")
    ?? listed[0];
  const actionCards = actionOrder.map((id) => actionCard(
    landing.actions.get(id)!,
    true,
    id === "cite" && citeExample ? `${citeExample.record.id}/index.html?tour=citation` : undefined,
  ));
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
<p class="stats-line">${plural(listed.length, "submission")} · ${plural(concepts.length, "concept")} · ${plural(statements.length, "statement")}, ${provenStatements} proven</p>
</div>
${tagBrowser}
<ul class="submissions-list" id="submissions-list">
${rows.join("\n")}
<li id="submissions-list-empty" class="submissions-list-empty" hidden>No submissions match.</li>
</ul>
<button class="submissions-load-more" id="submissions-load-more" type="button" aria-controls="submissions-list" hidden>Load more</button>
</section>`;
  const submit = `<section class="landing-action-panel landing-submit-panel latex-content" id="landing-panel-submit" aria-labelledby="landing-action-submit">
<p class="landing-action-eyebrow">Contribute to Lax</p>
<h3>Creating your own submission</h3>
${copyablePrompt(markdown.render(landing.submit, ""))}
</section>`;
  const reviewStarts = reviewConcepts.map(({ located, users, otherSubmissionCount, weight }, index) => `<div class="landing-review-start" data-review-concept="${attr(located.concept.id)}" data-review-weight="${weight}"${index ? " hidden" : ""}>
<div class="landing-review-start-copy">
<p class="landing-action-eyebrow">Used by ${plural(otherSubmissionCount, "other submission")} and ${plural(users.length, "other concept")}</p>
<h4>${markdown.renderAuthorInline(located.concept.title, "")}</h4>
<p>This concept is reused elsewhere in the archive. Review its mathematical correctness, endorse it if correct, or flag a flaw.</p>
</div>
<a class="landing-hero-button primary" href="${attr(`${located.output.id}/${located.concept.id}.html`)}">Review now <b aria-hidden="true">→</b></a>
</div>`).join("\n");
  const review = `<section class="landing-action-panel landing-review-panel" id="landing-panel-review" aria-labelledby="landing-action-review">
<p class="landing-action-eyebrow">Contribute a review</p>
<h3>Review a concept</h3>
${reviewStarts}
</section>`;
  const proofObligations = `<section class="landing-action-panel landing-proof-obligations-panel" id="landing-proof-obligations" aria-labelledby="landing-proof-obligations-heading">
<p class="landing-action-eyebrow">Contribute a proof</p>
<h3 id="landing-proof-obligations-heading">Open proof obligations</h3>
<p>${openProblems.length
    ? `Browse every claim that does not yet have a grounded proof, across ${plural(openProblemSubmissions, "submission")}.`
    : "Every claim currently has a grounded proof; this view will update automatically when a proof obligation is submitted."}</p>
<a class="landing-open-problems-link" href="open-proof-obligations.html"><span><strong>${openProblems.length}</strong> ${openProblems.length === 1 ? "proof obligation" : "proof obligations"}</span><b>Browse proof obligations <span aria-hidden="true">→</span></b></a>
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
${proofObligations}
</div>
</section>
${faq}`;
  return page({
    title: "Lax Lean Archive",
    rootRel: "",
    sidebar: indexSidebar(model, markdown, tagIndex.bySubmission),
    content,
    scripts: ["assets/landing.js"],
  });
}
