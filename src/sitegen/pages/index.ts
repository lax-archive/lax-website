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

interface ExcerptPassage {
  id: string;
  kind: "concept" | "proof";
  /** the passage as the aria label names it */
  label: string;
  /** the passage's text, Markdown with KaTeX */
  text: string;
  /** this passage's card opens with the page (default: the first one) */
  open?: boolean;
}

interface Excerpt {
  page: number;
  /** the prose before the passages, Markdown */
  before: string;
  passages: ExcerptPassage[];
  /** the prose after the passages, Markdown */
  after: string;
  /** link the "read" button to the first passage rather than the top */
  deepLink?: boolean;
}

// The two crops are the landing page's own telling of the introduction's
// running example, not the paper's text: the prose here is written for
// the boxes, the passages are typeset from the paper's statements
// (Markdown with KaTeX), and every card is the archive's real card for
// the concept or proof the paper marks.

/** Concepts: the definition of a prime and the two lemmas the headline
 * theorem will rest on. Lemma B is stated and left open. */
const INTRO_EXCERPT: Excerpt = {
  page: 1,
  before: `### 1 Concepts

A Lax submission states its mathematics as *concepts*: a definition or a claim in prose, paired with a faithful Lean encoding of exactly that statement. This section introduces three of them.`,
  passages: [
    {
      id: "Lax242665.Primes",
      kind: "concept",
      label: "Definition 1, prime numbers",
      text: "**Definition 1.** A natural number greater than 1 is *prime* if it is divisible only by 1 and by itself.",
    },
    {
      id: "Lax242665.OddPrimes",
      kind: "concept",
      label: "Lemma A, every prime other than 2 is odd",
      text: "**Lemma A.** *Every prime other than 2 is odd.*",
    },
    {
      id: "Lax242665.BertrandPostulate",
      kind: "concept",
      label: "Lemma B, Bertrand's postulate",
      text: "**Lemma B** (Bertrand's postulate)**.** *For every natural number $n \\geq 1$ there is a prime $p$ with $n < p \\leq 2n$.*",
    },
  ],
  after: `Each concept's card shows its Lean encoding. Even without knowing Lean, compare the two: whether the code says what the prose says is the one thing Lean cannot check, and the one thing a reviewer needs to. Note that Lemma B is stated as an \`axiom\`, without a proof — Lax separates stating a claim from proving it.`,
};

/** Proofs: the headline theorem, proven from Lemmas A and B; the proof's
 * card opens with the page, showing what the proof assumes and concludes. */
const INTRO_PROOF_EXCERPT: Excerpt = {
  page: 3,
  deepLink: true,
  before: `### 2 Proofs

A proof in Lax is Lean code that derives one concept from others. Lax does not display the code; it records, checked by Lean, which concepts the proof assumes and which it concludes. Here is the submission's main result.`,
  passages: [
    {
      id: "Lax242665.OddPrimeBetween",
      kind: "concept",
      label: "Theorem 2, an odd prime between n and 2n",
      text: "**Theorem 2.** *For every natural number $n \\geq 2$ there is an odd prime $p$ with $n < p \\leq 2n$.*",
    },
    {
      id: "Lax242665Proofs.OddPrimeBetween.exists_odd_prime_between",
      kind: "proof",
      label: "Proof of Theorem 2",
      open: true,
      text: "*Proof.* By Lemma B there is a prime $p$ with $n < p \\leq 2n$. Since $n \\geq 2$, we have $p > 2$, so $p$ is odd by Lemma A. $\\square$",
    },
  ],
  after: `The proof rests on Lemma A and Lemma B, and its card says so. Lemma A is proven in this submission; Lemma B is not, so Theorem 2 is proven *relative to* Lemma B until a follow-up submission supplies that proof — at which point both turn green, without anyone touching this submission.`,
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
  for (const heading of ["How it works", "Proofs", "Proof network", "What it is for"])
    if (!sections.has(heading)) throw new Error(`landing.md is missing the ${heading} section`);
  return { title: title[1]!.trim(), intro: head.slice(title[0].length).trim(), sections };
}

/** A section's paragraphs, split into the prose that stays in the text
 * column and the last paragraph, which is the caption of the figure the
 * section leads into (captions sit inside their box). */
function splitCaption(section: string): { body: string; caption: string } {
  const paragraphs = section.trim().split(/\n\s*\n/);
  const caption = paragraphs.pop() ?? "";
  return { body: paragraphs.join("\n\n"), caption };
}

/** A section of `### ` tiles: heading and Markdown body each. */
function landingTiles(heading: string, section: string, markdown: PageContext["markdown"]): string {
  const tiles = section.trim().split(/\n(?=### )/).map((chunk) => {
    const match = /^### ([^\n]+)\n+([\s\S]+)$/.exec(chunk.trim());
    if (!match) throw new Error(`invalid landing tile: ${chunk}`);
    return `<article class="landing-tile"><h3>${esc(match[1]!.trim())}</h3>
<div class="landing-tile-copy latex-content">
${markdown.render(match[2]!.trim(), "")}
</div>
</article>`;
  });
  return `<section class="landing-section landing-tiles-section" aria-labelledby="landing-tiles-heading">
<h2 class="landing-section-title" id="landing-tiles-heading">${esc(heading)}</h2>
<div class="landing-tiles">
${tiles.join("\n")}
</div>
</section>`;
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
 * encoding is on the page before anyone hovers; it is open, not pinned,
 * so the first hover away closes it and the usual behaviour takes over). landing.js sets each
 * card beside its passage and draws the band between them in the SVG
 * overlay, the way the paper page does; without it the cards stack in
 * the rail. */
async function paperExcerpt(ctx: PageContext, intro: SiteSubmission, excerpt: Excerpt, caption: string): Promise<string> {
  const { markdown } = ctx;
  const paper = intro.output!.paper!;
  const home = intro.record.id;
  const passages: string[] = [];
  const cards: string[] = [];
  let firstMark = 0;
  for (const [index, passage] of excerpt.passages.entries()) {
    const n = paper.marks.findIndex((mark) => mark.kind === passage.kind && mark.id === passage.id) + 1;
    if (!n) throw new Error(`the introduction's paper does not mark ${passage.id}`);
    const cardId = `landing-m${n}`;
    const first = excerpt.passages.some((p) => p.open) ? passage.open === true : index === 0;
    if (index === 0) firstMark = n;
    passages.push(`<div class="landing-passage landing-passage-${index + 1} kind-${passage.kind}${first ? " manuscript-hl-active" : ""}" role="button" tabindex="0" aria-pressed="false" aria-controls="${attr(cardId)}" aria-label="${attr(`${passage.label}: show the ${passage.kind} card`)}" data-excerpt-card="${attr(cardId)}" data-kind="${passage.kind}">
${markdown.render(passage.text, "")}
</div>`);
    cards.push(await markCard(ctx, paper.marks[n - 1]!, n, home, cardId, { rootRel: "", expanded: first }));
  }
  const href = `${home}/paper.html${excerpt.deepLink ? `#m${firstMark}` : ""}`;
  return `<section class="landing-box landing-paper manuscript" aria-label="${attr(`Page ${excerpt.page} of the annotated paper of ${home}, as the archive shows it`)}" data-card-box data-paper-excerpt>
<div class="landing-paper-frame">
<div class="landing-box-caption latex-content">
${markdown.render(caption, "")}
</div>
<div class="landing-paper-grid">
<div class="landing-paper-doc">
<div class="landing-paper-prose landing-paper-before latex-content">
${markdown.render(excerpt.before, "")}
</div>
${passages.join("\n")}
<div class="landing-paper-prose landing-paper-after latex-content">
${markdown.render(excerpt.after, "")}
</div>
</div>
<ol class="manuscript-rail landing-paper-rail" aria-label="Cards">
${cards.join("\n")}
</ol>
<svg class="manuscript-links landing-paper-links" aria-hidden="true"></svg>
</div>
<div class="landing-paper-foot"><a class="landing-paper-more" href="${attr(href)}">Read full introduction to Lax</a></div>
</div>
</section>`;
}

/** The introduction's proof network, drawn by dag.js from the same data
 * the submission page embeds, with links from the site root. */
function proofNetworkFigure(ctx: PageContext, intro: SiteSubmission, caption: string): string {
  const data = proofNetworkData(ctx, intro, "");
  return `<figure class="landing-box graph-figure proof-network-figure landing-network-figure" aria-label="${attr(`The proof network of ${intro.record.id}`)}">
<div class="landing-box-caption latex-content">
${ctx.markdown.render(caption, "")}
</div>
${graphExpandButton("proof network")}
<div id="proof-network" class="figure-container" data-graph="proofs"></div>
${graphTooltip()}
${proofNetworkLegend(data)}
</figure>
${graphDataScript({ proofs: data })}`;
}

/** The landing page: the manifesto from content/landing.md, then "How it
 * works" — its prose leading into the introduction submission's paper
 * excerpt and that submission's proof network, each box captioned by the
 * last paragraph of its section — the two ways in, the submissions library
 * with its stats, and the FAQ. Records that
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
    && [...INTRO_EXCERPT.passages, ...INTRO_PROOF_EXCERPT.passages].every((passage) =>
      submission.output!.paper!.marks.some((mark) => mark.kind === passage.kind && mark.id === passage.id)));
  const how = splitCaption(landing.sections.get("How it works")!);
  const proofsCopy = splitCaption(landing.sections.get("Proofs")!);
  const networkCopy = splitCaption(landing.sections.get("Proof network")!);
  const excerpt = intro ? await paperExcerpt(ctx, intro, INTRO_EXCERPT, how.caption) : "";
  const inference = intro ? await paperExcerpt(ctx, intro, INTRO_PROOF_EXCERPT, proofsCopy.caption) : "";
  const network = intro ? proofNetworkFigure(ctx, intro, networkCopy.caption) : "";

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
<p class="stats-line">${plural(listed.length, "submission")} · ${plural(concepts.length, "concept")} · ${plural(statements.length, "statement")}, ${provenStatements} proven</p>
</div>
${tagBrowser}
<ul class="submissions-list" id="submissions-list">
${rows.join("\n")}
<li id="submissions-list-empty" class="submissions-list-empty" hidden>No submissions match.</li>
</ul>
<button class="submissions-load-more" id="submissions-load-more" type="button" aria-controls="submissions-list" hidden>Show all ${plural(listed.length, "submission")} <b aria-hidden="true">↓</b></button>
</section>`;
  const introLink = intro
    ? `<a class="landing-hero-button primary landing-cta" href="${attr(`${intro.record.id}/paper.html`)}">Read the introduction to Lax</a>`
    : `<a class="landing-hero-button primary landing-cta" href="assets/lax-white-paper.pdf" download="lax-white-paper.pdf">Read the Lax paper</a>`;
  const links = `<nav class="landing-hero-actions" aria-label="Ways into Lax">
${introLink}
</nav>`;

  const content = `<section class="landing-hero" aria-labelledby="landing-title">
<h1 class="landing-title" id="landing-title">${esc(landing.title)}</h1>
<div class="landing-manifesto latex-content">
${markdown.render(landing.intro, "")}
</div>
</section>
<section class="landing-section landing-how" aria-labelledby="landing-how-heading">
<h2 class="landing-section-title" id="landing-how-heading">How it works</h2>
<div class="landing-section-copy latex-content">
${markdown.render(how.body, "")}
</div>
${excerpt}
${proofsCopy.body ? `<div class="landing-section-copy landing-proofs-copy latex-content">
${markdown.render(proofsCopy.body, "")}
</div>` : ""}
${inference}
${networkCopy.body ? `<div class="landing-section-copy landing-network-copy latex-content">
${markdown.render(networkCopy.body, "")}
</div>` : ""}
${network}
</section>
${links}
${landingTiles("What it is for", landing.sections.get("What it is for")!, markdown)}
<div class="landing-action-panels">
<h2 class="landing-section-title" id="landing-library-heading">Submissions</h2>
${library}
${faq}
</div>`;
  return page({
    title: "Lax Lean Archive",
    rootRel: "",
    sidebar: indexSidebar(model, markdown, tagIndex.bySubmission),
    content,
    detailClass: "detail-landing",
    sidebarHidden: true,
    scripts: intro ? ["assets/layout.js", "assets/dag.js", "assets/landing.js"] : ["assets/landing.js"],
  });
}
