import { attr, code, esc, formatDate, page, plural, proofBadge, statePill, typeBadge } from "../html.js";
import { contentMarkdown } from "../content.js";
import { graphDataScript } from "../graphs.js";
import { highlightSource } from "../highlight.js";
import { submissionTagIndex } from "../tags.js";
import type { SiteModel, SiteSubmission } from "../model.js";
import type { PaperMark, StatementEntry } from "../../types.js";
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

/** "An Introduction to Lax", itself a Lax submission with an annotated
 * paper: the header's "Introduction" and the first example's way on lead
 * into it. Without it in the archive (a preview from a fixture, a fork)
 * the header link is left out and the example leads to the white paper. */
export const INTRO_SUBMISSION_ID = "lax-242665";

/** The submission whose proof network the landing page draws: a real
 * paper's worth of claims and proofs, wide enough to show what the network
 * is for. Without it the page keeps the text and drops the figure. */
export const NETWORK_SUBMISSION_ID = "lax-17";

// ---- the worked examples ----
// Three excerpts of annotated papers, written for the landing page. The
// prose is the page's own. The cards are either the archive's own — the
// concept or proof of a named id, rendered exactly as the paper page
// renders it, linked to its page — or written here: complete, valid Lean
// for a small self-contained example, in the archive's card markup, linked
// nowhere. Nothing on a card is abbreviated. A proof card is its judgment
// alone: what it rests on, what it concludes.

interface ExampleConcept {
  kind: "concept";
  /** the name the card leads with */
  name: string;
  type: "definition" | "lemma" | "theorem";
  title: string;
  /** Markdown with KaTeX */
  description: string;
  /** the Lean, as a concept file minus its module docstring */
  lean: string;
}

interface ExampleProof {
  kind: "proof";
  name: string;
  /** names of the concept cards the proof rests on */
  assumptions: string[];
  /** name of the concept card it concludes */
  conclusion: string;
}

/** A card that is the archive's own: the concept or proof of that id,
 * rendered exactly as the paper page renders it. An example with such a
 * card stays off the page while the archive lacks the id. */
interface ExampleArchiveCard {
  kind: "archive";
  of: "concept" | "proof";
  id: string;
}

type ExampleCard = ExampleConcept | ExampleProof | ExampleArchiveCard;

interface ExamplePassage {
  /** the passage as the aria label names it */
  label: string;
  /** the passage's text, Markdown with KaTeX */
  text: string;
  card: ExampleCard;
}

interface Example {
  key: string;
  /** what the excerpt is, for the aria label */
  subject: string;
  /** the submission the example leads to, when the archive lists it */
  home?: string;
  passages: ExamplePassage[];
}

const lean = (lines: string[]): string => `${lines.join("\n")}\n`;

/** The prose around the passages: filler, so that nothing competes with
 * the definitions and claims for attention. Two lines fade in from the
 * top of the crop; a few fade out at its bottom. */
const BEFORE_PASSAGES = `Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.`;
const AFTER_PASSAGES = `Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.`;

const PRIMES_EXAMPLE: Example = {
  key: "primes",
  subject: "a paper on prime numbers",
  home: INTRO_SUBMISSION_ID,
  passages: [
    {
      label: "Definition 1, prime numbers",
      text: "**Definition 1.** A natural number greater than 1 is *prime* if it is divisible only by 1 and by itself.",
      card: {
        kind: "concept", name: "Primes", type: "definition", title: "Prime numbers",
        description: "A natural number greater than 1 is *prime* if it is divisible only by 1 and by itself.",
        lean: lean([
          "import Mathlib.Data.Nat.Notation",
          "",
          "namespace Primes",
          "",
          "/-- `n` is prime: it is greater than 1, and its only divisors are 1 and `n`",
          "itself. -/",
          "def Prime (n : ℕ) : Prop :=",
          "  1 < n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n",
          "",
          "end Primes",
        ]),
      },
    },
    {
      label: "Lemma A, every natural number greater than 1 has a prime divisor",
      text: "**Lemma A.** *Every natural number $n > 1$ has a prime divisor.*",
      card: {
        kind: "concept", name: "PrimeDivisor", type: "lemma", title: "Every number greater than 1 has a prime divisor",
        description: "Every natural number $n > 1$ has a prime divisor.",
        lean: lean([
          "import Primes",
          "",
          "namespace PrimeDivisor",
          "open Primes",
          "",
          "/-- Every natural number greater than 1 has a prime divisor. -/",
          "axiom exists_prime_dvd : ∀ n : ℕ, 1 < n → ∃ p, Prime p ∧ p ∣ n",
          "",
          "end PrimeDivisor",
        ]),
      },
    },
    {
      label: "Proof of Lemma A",
      text: "*Proof.* Let $d$ be the least divisor of $n$ with $d > 1$. Every divisor of $d$ divides $n$, so $d$ has no divisor strictly between 1 and $d$; hence $d$ is prime. $\\square$",
      card: {
        kind: "proof", name: "Proofs.PrimeDivisor", assumptions: [], conclusion: "PrimeDivisor",
      },
    },
    {
      label: "Theorem B, Euclid's theorem",
      text: "**Theorem B** (Euclid)**.** *For every $n$ there is a prime $p > n$.*",
      card: {
        kind: "concept", name: "Euclid", type: "theorem", title: "There are infinitely many primes",
        description: "For every natural number $n$ there is a prime number $p > n$.",
        lean: lean([
          "import Primes",
          "",
          "namespace Euclid",
          "open Primes",
          "",
          "/-- Beyond every natural number lies a prime. -/",
          "axiom exists_prime_gt : ∀ n : ℕ, ∃ p, Prime p ∧ n < p",
          "",
          "end Euclid",
        ]),
      },
    },
    {
      label: "Proof of Theorem B",
      text: "*Proof.* By Lemma A, $n! + 1$ has a prime divisor $p$. If $p \\leq n$, then $p$ divides $n!$ and hence divides 1, which is impossible. So $p > n$. $\\square$",
      card: {
        kind: "proof", name: "Proofs.Euclid", assumptions: ["PrimeDivisor"], conclusion: "Euclid",
      },
    },
  ],
};

const RAMSEY_EXAMPLE: Example = {
  key: "ramsey",
  subject: "a paper on Ramsey's theorem",
  home: "lax-14",
  passages: [
    {
      label: "Definition 1, cliques and independent sets",
      text: "**Definition 1.** A set $S \\subseteq V(G)$ is a *clique* if any two distinct vertices of $S$ are adjacent, and *independent* if no two are.",
      card: {
        kind: "concept", name: "Cliques", type: "definition", title: "Cliques and independent sets",
        description: "A set of vertices of a graph is a *clique* if any two distinct vertices in it are adjacent, and *independent* if no two are.",
        lean: lean([
          "import Mathlib.Combinatorics.SimpleGraph.Basic",
          "",
          "namespace Cliques",
          "",
          "variable {V : Type*} (G : SimpleGraph V)",
          "",
          "/-- Any two distinct vertices of `S` are adjacent. -/",
          "def IsClique (S : Set V) : Prop :=",
          "  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v",
          "",
          "/-- No two vertices of `S` are adjacent. -/",
          "def IsIndepSet (S : Set V) : Prop :=",
          "  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v",
          "",
          "end Cliques",
        ]),
      },
    },
    {
      label: "Theorem 2, Ramsey's theorem",
      text: "**Theorem 2** (Ramsey)**.** *For all $a$ and $b$ there is an $N$ such that every graph on at least $N$ vertices contains a clique of size $a$ or an independent set of size $b$.*",
      card: {
        kind: "concept", name: "Ramsey", type: "theorem", title: "Ramsey's theorem",
        description: "For all $a$ and $b$ there is an $N$ such that every graph on at least $N$ vertices contains a clique on $a$ vertices or an independent set on $b$ vertices.",
        lean: lean([
          "import Cliques",
          "import Mathlib.Data.Set.Card",
          "",
          "namespace Ramsey",
          "open Cliques",
          "",
          "/-- Ramsey's theorem: a large enough graph contains a clique on `a`",
          "vertices or an independent set on `b` vertices. -/",
          "axiom exists_clique_or_indepSet (a b : ℕ) :",
          "    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n →",
          "      (∃ S : Set (Fin n), IsClique G S ∧ a ≤ S.ncard) ∨",
          "      (∃ S : Set (Fin n), IsIndepSet G S ∧ b ≤ S.ncard)",
          "",
          "end Ramsey",
        ]),
      },
    },
  ],
};

const RAM_EXAMPLE: Example = {
  key: "ram",
  subject: "a paper on algorithms on a random access machine",
  home: "lax-11",
  passages: [
    {
      label: "Definition 1, the word RAM",
      text: "**Definition 1** (Word RAM)**.** A *word RAM* of word length $w$ has $2^w$ memory cells, each holding a number below $2^w$, a read-only input tape and a write-only output tape. A *program* is a finite sequence of instructions [...]; each instruction names the cells it operates on, and arithmetic wraps around modulo $2^w$. [...]",
      card: { kind: "archive", of: "concept", id: "Lax67.Ram" },
    },
    {
      label: "Definition 2, the encoding of a graph",
      text: "**Definition 2.** A graph $G$ on the vertices $0, \\ldots, n-1$ with $m$ edges is given to the machine as the word $n, m, o_0, \\ldots, o_n, t_0, \\ldots, t_{2m-1}$: the *offsets* $o_i$ cut the *target array* $t$ into one block per vertex, and the block of $u$ lists exactly the neighbours of $u$. [...]",
      card: { kind: "archive", of: "concept", id: "Lax11.GraphEncoding" },
    },
    {
      label: "Theorem 3, connected components in linear time",
      text: "**Theorem 3.** *There are a program and a constant $c$ such that, given any graph as in Definition 2 as a word $x$, the program halts within $c\\,(|x|+1)$ steps having written, for every vertex, the least vertex of its connected component.*",
      card: { kind: "archive", of: "concept", id: "Lax11.ConnectedComponents" },
    },
    {
      label: "Proof of Theorem 3",
      text: "*Proof.* The program scans the vertices in increasing order and runs a breadth-first search from each vertex not yet labelled, labelling everything it reaches with that vertex. [...] Every block of the target array is read once, so the running time is linear in $|x|$. $\\square$",
      card: { kind: "archive", of: "proof", id: "Lax11Proofs.CCMain.exists_linearTime_program_ccLabels" },
    },
  ],
};

const EXAMPLES: Example[] = [PRIMES_EXAMPLE, RAMSEY_EXAMPLE, RAM_EXAMPLE];

interface LandingCopy {
  title: string;
  /** the manifesto under the title, Markdown */
  intro: string;
  /** the `## ` sections by heading, Markdown */
  sections: Map<string, string>;
}

const LANDING_SECTIONS = ["How it works", "Proof network", "Get started right away", "Build foundations together"];

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
  for (const heading of LANDING_SECTIONS)
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

/** Getting started: one compact, accessible tab per supported host system. */
function landingSetupSection(heading: string, section: string, markdown: PageContext["markdown"]): string {
  const ids = new Map([["Linux / macOS", "unix"], ["Windows", "windows"]]);
  const tabs = section.trim().split(/\n(?=### )/).map((chunk) => {
    const match = /^### ([^\n]+)\n+([\s\S]+)$/u.exec(chunk.trim());
    if (!match) throw new Error(`invalid getting-started tab: ${chunk}`);
    const label = match[1]!.trim();
    const id = ids.get(label);
    if (!id) throw new Error(`unsupported getting-started tab: ${label}`);
    return { id, label, body: match[2]!.trim() };
  });
  for (const label of ids.keys())
    if (!tabs.some((tab) => tab.label === label)) throw new Error(`landing.md is missing the ${label} getting-started tab`);
  const controls = tabs.map(({ id, label }, index) =>
    `<button class="landing-setup-tab" type="button" role="tab" id="landing-setup-${id}-tab" aria-selected="${index === 0}" aria-controls="landing-setup-${id}-panel" tabindex="${index === 0 ? 0 : -1}">${esc(label)}</button>`);
  const panels = tabs.map(({ id, body }, index) => `<div class="landing-setup-panel landing-section-copy latex-content" id="landing-setup-${id}-panel" role="tabpanel" aria-labelledby="landing-setup-${id}-tab"${index === 0 ? "" : " hidden"}>
${markdown.render(body, "")}
</div>`);
  return `<section class="landing-section landing-plain-section landing-setup" aria-labelledby="landing-start-heading">
<h2 class="landing-section-title" id="landing-start-heading">${esc(heading)}</h2>
<div class="landing-section-box">
<div class="landing-setup-tabs" data-setup-tabs>
<div class="landing-setup-tab-list" role="tablist" aria-label="Choose your operating system">
${controls.join("\n")}
</div>
${panels.join("\n")}
</div>
</div>
</section>`;
}

/** The foundations section: its prose, then the concepts its list names
 * that the archive holds, each linked to its page with the number of
 * further submissions whose concepts build on it. Nothing when the archive
 * has none of them. */
function landingFoundations(ctx: PageContext, heading: string, section: string): string {
  const { model, markdown } = ctx;
  const lines = section.trim().split("\n");
  const ids = lines.filter((line) => /^- /.test(line)).map((line) => line.replace(/^- /, "").trim());
  const prose = lines.filter((line) => !/^- /.test(line)).join("\n").trim();
  const items = ids.flatMap((id) => {
    const located = model.conceptHome.get(id);
    if (!located) return [];
    const dependents = new Set(model.downstreamClosure(id).map((c) => c.output.id));
    dependents.delete(located.output.id);
    const uses = dependents.size ? `<span class="landing-foundation-uses">built on in ${plural(dependents.size, "further submission")}</span>` : "";
    return [`<li><a class="landing-foundation" href="${attr(`${located.output.id}/${located.concept.id}.html`)}" title="${attr(located.concept.id)}">
${typeBadge(located.concept.type)}<span class="landing-foundation-title">${markdown.renderAuthorInline(located.concept.title, "")}</span>
<span class="landing-foundation-meta"><span class="submission-meta-id">${esc(located.output.id)}</span>${uses}</span>
</a></li>`];
  });
  if (!items.length) return "";
  return `<section class="landing-section landing-foundations" aria-labelledby="landing-foundations-heading">
<h2 class="landing-section-title" id="landing-foundations-heading">${esc(heading)}</h2>
<div class="landing-section-box">
<div class="landing-section-copy latex-content">
${markdown.render(prose, "")}
</div>
<ul class="landing-foundation-list">
${items.join("\n")}
</ul>
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

  return `<h2 class="landing-section-title landing-faq-title" id="landing-faq-heading">${esc(faq.title)}</h2>
<section class="landing-faq" id="faq" aria-labelledby="landing-faq-heading">
<ol class="landing-faq-list">
${items}
</ol>
</section>`;
}


/** The line range of the one declaration a claim's Lean states, for the
 * proven/open colouring of its rows: from the `axiom` line to the blank
 * line after it. */
function statementRange(source: string): [number, number] | undefined {
  const lines = source.split("\n");
  const start = lines.findIndex((line) => line.startsWith("axiom "));
  if (start < 0) return undefined;
  let end = start;
  while (end + 1 < lines.length && lines[end + 1]!.trim() !== "") end += 1;
  return [start + 1, end + 1];
}

/** Whether the archive holds every card the example borrows from it. */
function exampleAvailable(model: SiteModel, example: Example): boolean {
  return example.passages.every(({ card }) => card.kind !== "archive"
    || (card.of === "concept" ? model.conceptHome.has(card.id) : model.proofHome.has(card.id)));
}

/** An archive card of an example: the paper page's card for the concept
 * or proof, linked from the site root; a proof's card is its judgment
 * alone. */
async function archiveCard(ctx: PageContext, card: ExampleArchiveCard, n: number, cardId: string, expanded: boolean): Promise<string> {
  const home = card.of === "concept" ? ctx.model.conceptHome.get(card.id)?.output.id : ctx.model.proofHome.get(card.id)?.output.id;
  if (!home) throw new Error(`the archive does not hold ${card.id}`);
  const point = { page: 1, x: 0, y: 0, mode: "v" as const };
  const mark: PaperMark = { id: card.id, kind: card.of, begin: point, end: point };
  return markCard(ctx, mark, n, home, cardId, { rootRel: "", expanded, proofDescription: false });
}

/** A claim of the example as a judgment names it: badge and name. Every
 * claim of the examples counts as proven — each is proven in the
 * archive's version of the example — so the badge carries the mark. */
function exampleClaim(concept: ExampleConcept): string {
  return `<span class="claim-entry">${typeBadge(concept.type, true)}${code(concept.name)}</span>`;
}

/** One card of an example: the archive's own for an archive card, else
 * the same markup (the paper page's `markCard`) around the concept's
 * title, description and Lean, or the proof's judgment. Each concept
 * states one claim, which the card's head already names, so there is no
 * claims list. */
async function exampleCard(ctx: PageContext, example: Example, passage: ExamplePassage, n: number, cardId: string, expanded: boolean): Promise<string> {
  const { markdown } = ctx;
  const { card } = passage;
  if (card.kind === "archive") return archiveCard(ctx, card, n, cardId, expanded);
  const concepts = new Map(example.passages.flatMap((p) => p.card.kind === "concept" ? [[p.card.name, p.card] as const] : []));
  let badge: string;
  let body: string;
  if (card.kind === "concept") {
    const range = card.type === "definition" ? undefined : statementRange(card.lean);
    const statements: StatementEntry[] = range
      ? [{ id: `${card.name}.statement`, signature: "", startLine: range[0], endLine: range[1] }]
      : [];
    badge = typeBadge(card.type, statements.length ? true : undefined);
    const rows = await highlightSource(card.lean, statements, new Set(statements.map((s) => s.id)), { anchors: false });
    body = `<p class="manuscript-card-title">${markdown.renderAuthorInline(card.title, "")}</p>
<div class="latex-content">${markdown.renderAuthorProse(card.description, "")}</div>
<div class="manuscript-card-source"><div class="inline-contract-wrap"><table class="inline-contract-table">
${rows}
</table></div></div>`;
  } else {
    badge = proofBadge();
    const assumed = card.assumptions.map((name) => {
      const concept = concepts.get(name);
      if (!concept) throw new Error(`example ${example.key}: proof ${card.name} assumes an unknown card ${name}`);
      return `<li>${exampleClaim(concept)}</li>`;
    });
    const conclusion = concepts.get(card.conclusion);
    if (!conclusion) throw new Error(`example ${example.key}: proof ${card.name} concludes an unknown card ${card.conclusion}`);
    body = `<div class="judgment">
<div class="judgment-assumptions">${assumed.length ? `<ul>${assumed.join("\n")}</ul>` : `<p class="judgment-unconditional">no assumptions</p>`}</div>
<span class="judgment-arrow" aria-hidden="true">→</span>
<div class="judgment-conclusion">${exampleClaim(conclusion)}</div>
</div>`;
  }
  return `<li class="manuscript-card kind-${card.kind} line-proven${expanded ? " manuscript-card-expanded" : ""}" id="${attr(cardId)}">
<div class="manuscript-card-head">
<span class="manuscript-card-swatch" aria-hidden="true"></span>
<span class="manuscript-card-name">${badge}${code(card.name)}</span>
<button class="manuscript-card-toggle" type="button" aria-expanded="${expanded}" aria-controls="${attr(`${cardId}-body`)}" aria-label="${attr(`Show details of ${card.name}`)}"><span aria-hidden="true">▸</span></button>
</div>
<div class="manuscript-card-body" id="${attr(`${cardId}-body`)}"${expanded ? "" : " hidden"}>
${body}
</div>
</li>`;
}

/** One example as a slide: the prose around the passages in the text
 * column, each passage highlighted as on the paper page, and its card,
 * closed, in the rail beside it, with a hint under the cards saying what
 * to do (it goes with the first hover or tap). landing.js sets each card
 * beside its passage and draws the band between them in the SVG overlay,
 * the way the paper page does — on a phone it sets each card under its
 * passage instead; without it the cards stack in the rail. */
async function exampleSlide(ctx: PageContext, example: Example, listed: SiteSubmission[], selected: boolean): Promise<string> {
  const { markdown } = ctx;
  const passages: string[] = [];
  const cards: string[] = [];
  for (const [index, passage] of example.passages.entries()) {
    const cardId = `landing-${example.key}-${index + 1}`;
    const kind = passage.card.kind === "archive" ? passage.card.of : passage.card.kind;
    passages.push(`<div class="landing-passage landing-passage-${index + 1} kind-${kind}" role="button" tabindex="0" aria-pressed="false" aria-controls="${attr(cardId)}" aria-label="${attr(`${passage.label}: show the ${kind} card`)}" data-excerpt-card="${attr(cardId)}" data-kind="${kind}">
${markdown.render(passage.text, "")}
</div>`);
    cards.push(await exampleCard(ctx, example, passage, index + 1, cardId, false));
  }
  // The way on: the introduction's paper for the first example (the white
  // paper without it), the submission page for one drawn from the archive.
  const home = example.home ? listed.find((submission) => submission.record.id === example.home) : undefined;
  const more = example.home === INTRO_SUBMISSION_ID
    ? (home
      ? `<a class="landing-paper-more" href="${attr(`${home.record.id}/paper.html`)}">Read full introduction to Lax</a>`
      : `<a class="landing-paper-more" href="assets/lax-white-paper.pdf" download="lax-white-paper.pdf">Read the Lax paper</a>`)
    : home
      ? `<a class="landing-paper-more" href="${attr(`${home.record.id}/index.html`)}">See full submission</a>`
      : "";
  const foot = more ? `<div class="landing-paper-foot">${more}</div>` : "";
  return `<div class="landing-carousel-slide${selected ? "" : " landing-carousel-slide-off"}" role="tabpanel" id="${attr(`landing-example-${example.key}`)}" aria-labelledby="${attr(`landing-tab-${example.key}`)}"${selected ? "" : ` aria-hidden="true" inert`} data-card-box data-paper-excerpt>
<div class="landing-paper-grid">
<div class="landing-paper-doc">
<div class="landing-paper-prose landing-paper-before latex-content">
${markdown.render(BEFORE_PASSAGES, "")}
</div>
${passages.join("\n")}
<div class="landing-paper-prose landing-paper-after latex-content">
${markdown.render(AFTER_PASSAGES, "")}
</div>
</div>
<ol class="manuscript-rail landing-paper-rail" aria-label="Cards">
${cards.join("\n")}
<li class="landing-paper-hint" aria-hidden="true"><span class="landing-paper-hint-hover">Hover a highlight to expand</span><span class="landing-paper-hint-touch">Tap a highlight to expand</span></li>
</ol>
<svg class="manuscript-links landing-paper-links" aria-hidden="true"></svg>
${foot}
</div>
</div>`;
}

/** The examples box: the caption at the top left with a dot per
 * example beside it, the slides below, and a large arrow at either side
 * of the box, centred on the slides, to step through them. landing.js
 * shows one slide at a time (the arrow keys step too); without it the
 * first example shows. Every slide ends in the way on: the introduction,
 * or the submission. */
async function examplesBox(ctx: PageContext, listed: SiteSubmission[], caption: string): Promise<string> {
  const examples = EXAMPLES.filter((example) => exampleAvailable(ctx.model, example));
  const dots = examples.map((example, index) =>
    `<button class="landing-carousel-dot" role="tab" type="button" id="${attr(`landing-tab-${example.key}`)}" aria-selected="${index === 0}" aria-controls="${attr(`landing-example-${example.key}`)}" aria-label="${attr(`Example ${index + 1} of ${examples.length}: ${example.subject}`)}" tabindex="${index === 0 ? 0 : -1}"></button>`);
  const slides: string[] = [];
  for (const [index, example] of examples.entries()) slides.push(await exampleSlide(ctx, example, listed, index === 0));
  const tablist = examples.length > 1 ? `<div class="landing-carousel-dots" role="tablist" aria-label="Examples">
${dots.join("\n")}
</div>` : "";
  const arrows = examples.length > 1 ? `<div class="landing-carousel-arrows">
<button class="landing-carousel-arrow landing-carousel-arrow-prev" type="button" data-carousel-step="-1" aria-label="Previous example" title="Previous example (←)"><span aria-hidden="true">‹</span></button>
<button class="landing-carousel-arrow landing-carousel-arrow-next" type="button" data-carousel-step="1" aria-label="Next example" title="Next example (→)"><span aria-hidden="true">›</span></button>
</div>` : "";
  return `<section class="landing-box landing-paper manuscript" aria-label="${attr(`Excerpts of ${plural(examples.length, "annotated paper")}, as the archive shows them: ${examples.map((e) => e.subject).join(", ")}`)}" data-carousel>
<div class="landing-paper-frame">
<div class="landing-box-head">
<div class="landing-box-caption latex-content">
${ctx.markdown.render(caption, "")}
</div>
${tablist}
</div>
<div class="landing-carousel-slides">
${arrows}
${slides.join("\n")}
</div>
</div>
</section>`;
}

/** A submission's proof network, drawn by dag.js from the same data the
 * submission page embeds, with links from the site root. The container
 * is centred and faded at its sides by landing.js and the stylesheet. */
function proofNetworkFigure(ctx: PageContext, submission: SiteSubmission, caption: string): string {
  const data = proofNetworkData(ctx, submission, "");
  const id = submission.record.id;
  return `<figure class="landing-box graph-figure proof-network-figure landing-network-figure" aria-label="${attr(`The proof network of ${id}`)}">
<div class="landing-box-caption latex-content">
${ctx.markdown.render(caption, "")}
</div>
${graphExpandButton("proof network")}
<div class="landing-network-viewport">
<div id="proof-network" class="figure-container" data-graph="proofs"></div>
</div>
${graphTooltip()}
${proofNetworkLegend(data)}
</figure>
${graphDataScript({ proofs: data })}`;
}

/** The landing page: the manifesto from content/landing.md, then "How it
 * works" — its prose leading into the examples box — and "Proof network"
 * — its prose leading into a submission's network — each box captioned by
 * the last paragraph of its section; getting started; the foundations the
 * archive builds on; the submissions library with its stats; and the FAQ. Records that only reserved an id
 * have nothing to show and stay off the library and the stats (their
 * pages exist for direct links). */
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
  const networkSubmission = listed.find((submission) => submission.record.id === NETWORK_SUBMISSION_ID && submission.output?.proofs.length);
  const how = splitCaption(landing.sections.get("How it works")!);
  const networkCopy = splitCaption(landing.sections.get("Proof network")!);
  const examples = await examplesBox(ctx, listed, how.caption);
  const network = networkSubmission ? proofNetworkFigure(ctx, networkSubmission, networkCopy.caption) : "";

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
  const content = `<section class="landing-hero" aria-labelledby="landing-title">
<h1 class="landing-title" id="landing-title">${esc(landing.title)}</h1>
<div class="landing-manifesto latex-content">
${markdown.render(landing.intro, "")}
</div>
</section>
<section class="landing-section landing-how" aria-labelledby="landing-how-heading">
<h2 class="landing-section-title" id="landing-how-heading">How it works</h2>
${how.body ? `<div class="landing-section-copy latex-content">
${markdown.render(how.body, "")}
</div>` : ""}
${examples}
${networkCopy.body ? `<div class="landing-section-copy landing-network-copy latex-content">
${markdown.render(networkCopy.body, "")}
</div>` : ""}
${network}
</section>
${landingSetupSection("Get started right away", landing.sections.get("Get started right away")!, markdown)}
${landingFoundations(ctx, "Build foundations together", landing.sections.get("Build foundations together")!)}
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
    landingHeader: true,
    scripts: network ? ["assets/layout.js", "assets/dag.js", "assets/landing.js"] : ["assets/landing.js"],
  });
}
