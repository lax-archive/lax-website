import { contentMarkdown } from "../content.js";
import { attr, esc, page } from "../html.js";
import type { PageContext } from "./shared.js";

const FORM_URL = "https://docs.google.com/forms/d/e/1FAIpQLScCkCORYWuaP9SvNeySxIsa_zEuqTz8q_d9b8-3SOxS1L_xIg/viewform?embedded=true";
const FORM_FRAME_ORIGINS = [new URL(FORM_URL).origin, "https://accounts.google.com"];
const SECTION_HEADINGS = ["What you will learn", "Workshop details", "Preregistration"] as const;

interface WorkshopCopy {
  title: string;
  introduction: string;
  sections: Map<string, string>;
}

function workshopCopy(source: string): WorkshopCopy {
  const chunks = source.trim().split(/\n(?=## )/);
  const introduction = /^# ([^\n]+)\n+([\s\S]+)$/.exec((chunks.shift() ?? "").trim());
  if (!introduction) throw new Error("workshop.md must start with a title and introduction");

  const sections = new Map<string, string>();
  for (const chunk of chunks) {
    const match = /^## ([^\n]+)\n+([\s\S]+)$/.exec(chunk.trim());
    if (!match) throw new Error(`invalid workshop section: ${chunk}`);
    sections.set(match[1]!.trim(), match[2]!.trim());
  }
  for (const heading of SECTION_HEADINGS) {
    if (!sections.has(heading)) throw new Error(`workshop.md is missing the ${heading} section`);
  }

  return {
    title: introduction[1]!.trim(),
    introduction: introduction[2]!.trim(),
    sections,
  };
}

/** The public workshop invitation and its Google Forms preregistration. */
export function workshopPage({ markdown }: PageContext): string {
  const copy = workshopCopy(contentMarkdown("workshop.md"));
  const section = (heading: typeof SECTION_HEADINGS[number]) => copy.sections.get(heading)!;
  const content = `<article class="workshop-page">
<header class="workshop-hero">
<p class="workshop-kicker">Free online workshop <span aria-hidden="true">·</span> laxarchive.org/workshop</p>
<h1>${esc(copy.title)}</h1>
<div class="workshop-lede latex-content">
${markdown.render(copy.introduction, "../")}
</div>
<ul class="workshop-highlights" aria-label="Workshop at a glance">
<li><span aria-hidden="true">✓</span> Free</li>
<li><span aria-hidden="true">◷</span> Two hours</li>
<li><span aria-hidden="true">◎</span> Live online</li>
<li><span aria-hidden="true">◇</span> All Lean levels</li>
</ul>
</header>
<div class="workshop-summary">
<section class="workshop-panel workshop-outcomes" aria-labelledby="workshop-outcomes-heading">
<p class="workshop-section-number" aria-hidden="true">01</p>
<h2 id="workshop-outcomes-heading">What you will learn</h2>
<div class="latex-content">
${markdown.render(section("What you will learn"), "../")}
</div>
</section>
<section class="workshop-panel workshop-details" aria-labelledby="workshop-details-heading">
<p class="workshop-section-number" aria-hidden="true">02</p>
<h2 id="workshop-details-heading">Workshop details</h2>
<div class="latex-content">
${markdown.render(section("Workshop details"), "../")}
</div>
</section>
</div>
<section class="workshop-registration" aria-labelledby="workshop-registration-heading">
<header class="workshop-registration-head">
<div>
<p class="workshop-section-number" aria-hidden="true">03</p>
<h2 id="workshop-registration-heading">Preregistration</h2>
</div>
<div class="workshop-registration-copy latex-content">
${markdown.render(section("Preregistration"), "../")}
<a class="workshop-form-link" href="${attr(FORM_URL)}" target="_blank" rel="noopener noreferrer">Open preregistration form <span aria-hidden="true">↗</span></a>
</div>
</header>
<div class="workshop-form-frame">
<iframe src="${attr(FORM_URL)}" width="100%" height="1100" frameborder="0" title="Lean and Lax workshop preregistration form">Loading…</iframe>
</div>
</section>
</article>`;
  return page({
    title: `${copy.title} — Lax Lean Archive`,
    rootRel: "../",
    sidebar: "",
    content,
    detailClass: "detail-workshop",
    frameOrigins: FORM_FRAME_ORIGINS,
  });
}
