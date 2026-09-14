import { contentMarkdown } from "../content.js";
import { attr, esc, page } from "../html.js";
import type { PageContext } from "./shared.js";

const FORM_URL = "https://docs.google.com/forms/d/e/1FAIpQLScCkCORYWuaP9SvNeySxIsa_zEuqTz8q_d9b8-3SOxS1L_xIg/viewform?embedded=true";
const FORM_FRAME_ORIGINS = [new URL(FORM_URL).origin, "https://accounts.google.com"];
const OUTCOMES_HEADING = "We offer a free online workshop that teaches:";
const SECTION_HEADINGS = [OUTCOMES_HEADING, "Workshop details"] as const;

interface WorkshopCopy {
  title: string;
  sections: Map<string, string>;
}

function workshopCopy(source: string): WorkshopCopy {
  const chunks = source.trim().split(/\n(?=## )/);
  const title = /^# ([^\n]+)$/.exec((chunks.shift() ?? "").trim());
  if (!title) throw new Error("workshop.md must start with a title");

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
    title: title[1]!.trim(),
    sections,
  };
}

/** The public workshop invitation and its Google Forms preregistration. */
export function workshopPage({ markdown }: PageContext): string {
  const copy = workshopCopy(contentMarkdown("workshop.md"));
  const section = (heading: typeof SECTION_HEADINGS[number]) => copy.sections.get(heading)!;
  const content = `<article class="workshop-page">
<header class="workshop-hero">
<h1>${esc(copy.title)}</h1>
<ul class="workshop-highlights" aria-label="Workshop at a glance">
<li><span aria-hidden="true">✓</span> Free</li>
<li><span aria-hidden="true">◷</span> Two hours</li>
<li><span aria-hidden="true">◎</span> Live online</li>
<li><span aria-hidden="true">◇</span> No Lean knowledge needed</li>
</ul>
</header>
<div class="workshop-summary">
<section class="workshop-panel workshop-outcomes" aria-labelledby="workshop-outcomes-heading">
<p class="workshop-section-number" aria-hidden="true">01</p>
<h2 id="workshop-outcomes-heading">${esc(OUTCOMES_HEADING)}</h2>
<div class="latex-content">
${markdown.render(section(OUTCOMES_HEADING), "../")}
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
<section class="workshop-registration" aria-label="Workshop registration">
<div class="workshop-form-frame">
<iframe src="${attr(FORM_URL)}" width="640" height="779" frameborder="0" marginheight="0" marginwidth="0" title="Lean and Lax workshop preregistration form">Loading…</iframe>
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
