import { attr, esc, formatDate, page, plural, statePill } from "../html.js";
import { contentMarkdown } from "../content.js";
import { graphDataScript } from "../graphs.js";
import { submissionTagIndex } from "../tags.js";
import type { SiteSubmission } from "../model.js";
import {
  currentSubmissions,
  graphExpandButton,
  graphTooltip,
  indexSidebar,
  proofNetworkLegend,
  submissionSearchAttributes,
  type PageContext,
} from "./shared.js";
import { markCard } from "./paper.js";
import { proofNetworkData } from "./submission.js";

interface LandingFaq { question: string; answer: string }

/** The submission the landing page shows Lax with: "An Introduction to
 * Lax", itself a Lax submission with an annotated paper. Its first page
 * is the excerpt, its proofs are the network. Without it in the archive
 * (a preview from a fixture, a fork) the page keeps the text and drops
 * the two figures and the link into the paper. */
export const INTRO_SUBMISSION_ID = "lax-242665";

/** The cropped paper: what page 1 says around its first two marked
 * passages, in the paper's own words (the passages are typeset here from
 * the same LaTeX, in Markdown with KaTeX), each passage joined to the
 * archive's card for the concept it marks. */
const INTRO_EXCERPT = {
  page: 1,
  before: `### 1 Concepts

Lax represents mathematical definitions and claims as so-called *concepts*. A concept pairs a natural-language statement, as it would appear in a paper, with a faithful encoding of that statement in Lean. This section is annotated with two of them, shown on the right.`,
  passages: [
    {
      id: "Lax242665.Primes",
      label: "Definition 1, prime numbers",
      text: "**Definition 1.** A natural number greater than 1 is *prime* if it is divisible only by 1 and by itself.",
    },
    {
      id: "Lax242665.InfinitelyManyPrimes",
      label: "Theorem 1, Euclid",
      text: "**Theorem 1** (Euclid)**.** *For every natural number $n$ there is a prime $p > n$.*",
    },
  ],
  after: `Even if you are not familiar with Lean, try reading the Lean code to see whether it encodes the intended meaning. One thing stands out: Theorem 1 is stated not as a \`theorem\` but as an \`axiom\`, without a proof. That is Lax's way of separating claims from proofs. The correctness of a formal proof is guaranteed by Lean, so with Lax, readers only review the one thing Lean can *not* check: whether the Lean code faithfully represents the intended mathematics.`,
};

interface LandingCopy {
  title: string;
  /** the manifesto under the title, Markdown */
  intro: string;
  /** the `## ` sections by heading, Markdown */
  sections: Map<string, string>;
}

function landingCopy(source: string): LandingCopy {
  const chunks = source.trim().split(/\n(?=## )/);
  const head = chunks.shift() ?? "";
  const title = /^# ([^\n]+)\n/.exec(head);
  if (!title) throw new Error("landing.md must start with a title");
  const sections = new Map<string, string>();
  for (const chunk of chunks) {
    const match = /^## ([^\n]+)\n+([\s\S]+)$/.exec(chunk.trim());
    if (!match) throw new Error(`invalid landing section: ${chunk}`);
    sections.set(match[1]!.trim(), match[2]!.trim());
  }
  for (const heading of ["Concepts", "Proof network"])
    if (!sections.has(heading)) throw new Error(`landing.md is missing the ${heading} section`);
  return { title: title[1]!.trim(), intro: head.slice(title[0].length).trim(), sections };
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

/** The paper excerpt: the prose around the passages in the text column,
 * each marked passage highlighted as on the paper page, and the archive's
 * own card for the concept beside it (the first one open, so the Lean
 * encoding is on the page before anyone hovers). landing.js sets each
 * card beside its passage the way the paper page does; without it the
 * cards stack in the rail. */
async function paperExcerpt(ctx: PageContext, intro: SiteSubmission): Promise<string> {
  const { markdown } = ctx;
  const paper = intro.output!.paper!;
  const home = intro.record.id;
  const passages: string[] = [];
  const cards: string[] = [];
  for (const [index, passage] of INTRO_EXCERPT.passages.entries()) {
    const n = paper.marks.findIndex((mark) => mark.kind === "concept" && mark.id === passage.id) + 1;
    if (!n) throw new Error(`the introduction's paper does not mark ${passage.id}`);
    const cardId = `landing-m${n}`;
    const first = index === 0;
    passages.push(`<div class="landing-passage landing-passage-${index + 1} kind-concept${first ? " manuscript-hl-active" : ""}" role="button" tabindex="0" aria-pressed="${first}" aria-controls="${attr(cardId)}" aria-label="${attr(`${passage.label}: show the concept card`)}" data-excerpt-card="${attr(cardId)}">
${markdown.render(passage.text, "")}
</div>`);
    cards.push(await markCard(ctx, paper.marks[n - 1]!, n, home, cardId, { rootRel: "", expanded: first }));
  }
  const title = markdown.renderAuthorInline(intro.output!.manifest.title, "");
  return `<section class="landing-paper manuscript" aria-labelledby="landing-paper-heading" data-paper-excerpt>
<p class="landing-action-eyebrow" id="landing-paper-heading">Annotated paper</p>
<p class="landing-paper-caption">Page ${INTRO_EXCERPT.page} of <a href="${attr(`${home}/paper.html`)}"><cite>${title}</cite></a>, as the archive shows it: hover a highlighted passage to open the concept it is annotated with.</p>
<div class="landing-paper-frame">
<div class="landing-paper-grid">
<div class="landing-paper-doc">
<div class="landing-paper-prose latex-content">
${markdown.render(INTRO_EXCERPT.before, "")}
</div>
${passages.join("\n")}
<div class="landing-paper-prose latex-content">
${markdown.render(INTRO_EXCERPT.after, "")}
</div>
</div>
<ol class="manuscript-rail landing-paper-rail" aria-label="Concept cards">
${cards.join("\n")}
</ol>
</div>
</div>
</section>`;
}

/** The introduction's proof network, drawn by dag.js from the same data
 * the submission page embeds, with links from the site root. */
function proofNetworkFigure(ctx: PageContext, intro: SiteSubmission): string {
  const data = proofNetworkData(ctx, intro, "");
  const title = ctx.markdown.renderAuthorInline(intro.output!.manifest.title, "");
  return `<figure class="graph-figure proof-network-figure landing-network-figure">
${graphExpandButton("proof network")}
<div id="proof-network" class="figure-container" data-graph="proofs"></div>
${graphTooltip()}
${proofNetworkLegend(data)}
</figure>
<p class="landing-paper-caption">The proof network of <a href="${attr(`${intro.record.id}/index.html`)}"><cite>${title}</cite></a>: each box is a claim, green once proven and yellow while open; each <span class="legend-proof-chip-inline" aria-hidden="true">⊢</span> chip is a proof deriving its conclusion from its assumptions. Click a node to open its page.</p>
${graphDataScript({ proofs: data })}`;
}

/** The landing page: the manifesto from content/landing.md, the paper
 * excerpt and proof network of the introduction submission, the two ways
 * in, the submissions library with its stats, and the FAQ. Records that
 * only reserved an id have nothing to show and stay off the library and
 * the stats (their pages exist for direct links). */
export async function indexPage(ctx: PageContext): Promise<string> {
  const { model, markdown } = ctx;
  const listed = currentSubmissions(model);
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
  const landing = landingCopy(contentMarkdown("landing.md"));
  const faq = landingFaq(contentMarkdown("faq.md"), markdown);
  const intro = listed.find((submission) => submission.record.id === INTRO_SUBMISSION_ID
    && submission.output?.paper
    && INTRO_EXCERPT.passages.every((passage) => submission.output!.paper!.marks.some((mark) => mark.kind === "concept" && mark.id === passage.id)));
  const excerpt = intro ? await paperExcerpt(ctx, intro) : "";
  const network = intro ? proofNetworkFigure(ctx, intro) : "";

  const chip = (key: string, label: string, count: number, extraClass = ""): string =>
    `<button class="tag-chip${extraClass}" type="button" data-tag-filter="${attr(key)}" aria-pressed="false" aria-label="${attr(`${label}, ${plural(count, "submission")}`)}"><span>${esc(label)}</span><b aria-hidden="true">${count}</b></button>`;
  // The environment is one more chip in the same strip: the browser filters
  // on `data-tags`, which carries it, so a flat facet needs no second control.
  // It appears only once the archive holds work in more than one environment —
  // before that the single chip would name the only thing there is. The chips
  // lead the strip because the strip is clipped to three rows.
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
  const library = `<section class="landing-action-panel submissions-library" id="landing-panel-read" aria-labelledby="landing-library-heading">
<div class="landing-action-panel-heading">
<p class="landing-action-eyebrow">Read the archive</p>
<h3 id="landing-library-heading">Submissions</h3>
<p class="stats-line">${plural(listed.length, "submission")} · ${plural(concepts.length, "concept")} · ${plural(statements.length, "statement")}, ${provenStatements} proven</p>
</div>
${tagBrowser}
<ul class="submissions-list" id="submissions-list">
${rows.join("\n")}
<li id="submissions-list-empty" class="submissions-list-empty" hidden>No submissions match.</li>
</ul>
<button class="submissions-load-more" id="submissions-load-more" type="button" aria-controls="submissions-list" hidden>Load more</button>
</section>`;
  const introLink = intro
    ? `<a class="landing-hero-button primary" href="${attr(`${intro.record.id}/paper.html`)}">Read the introduction to Lax <b aria-hidden="true">→</b></a>`
    : `<a class="landing-hero-button primary" href="assets/lax-white-paper.pdf" download="lax-white-paper.pdf">Read the Lax paper <b aria-hidden="true">↗</b></a>`;
  const links = `<nav class="landing-hero-actions" aria-label="Ways into Lax">
${introLink}
<button class="landing-hero-button secondary" type="button" data-landing-action="read" aria-controls="landing-panel-read">Browse submissions <b aria-hidden="true">↓</b></button>
</nav>
${intro ? `<p class="landing-links-note">The introduction is itself a Lax submission: every feature it describes is at work on its own pages.</p>` : ""}`;

  const content = `<section class="landing-hero" aria-labelledby="landing-title">
<h1 class="landing-title" id="landing-title">${esc(landing.title)}</h1>
<div class="landing-manifesto latex-content">
${markdown.render(landing.intro, "")}
</div>
</section>
${excerpt}
<section class="landing-section landing-concepts" aria-labelledby="landing-concepts-heading">
<h2 class="landing-section-title" id="landing-concepts-heading">Concepts</h2>
<div class="landing-section-copy latex-content">
${markdown.render(landing.sections.get("Concepts")!, "")}
</div>
</section>
<section class="landing-section landing-network" aria-labelledby="landing-network-heading">
<h2 class="landing-section-title" id="landing-network-heading">Proof network</h2>
<div class="landing-section-copy latex-content">
${markdown.render(landing.sections.get("Proof network")!, "")}
</div>
${network}
</section>
${links}
<div class="landing-action-panels">
${library}
${faq}
</div>`;
  return page({
    title: "Lax Lean Archive",
    rootRel: "",
    sidebar: indexSidebar(model, markdown, tagIndex.bySubmission),
    content,
    scripts: intro ? ["assets/layout.js", "assets/dag.js", "assets/landing.js"] : ["assets/landing.js"],
  });
}
