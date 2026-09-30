import { contentMarkdown } from "../content.js";
import { attr, esc, page } from "../html.js";
import type { PageContext } from "./shared.js";

const FORM_URL = "https://docs.google.com/forms/d/e/1FAIpQLScCkCORYWuaP9SvNeySxIsa_zEuqTz8q_d9b8-3SOxS1L_xIg/viewform?embedded=true";
const VIDEO_URL = "https://www.youtube-nocookie.com/embed/vx1IRXcA2bg";
const FORM_FRAME_ORIGINS = [new URL(FORM_URL).origin, "https://accounts.google.com", new URL(VIDEO_URL).origin];
const SLIDES_FILE = "lax-online-meeting-2026-09-30.pdf";
const OUTCOMES_HEADING = "We invite you to an online meeting";
const MATERIAL_HEADING = "Material from the 1st Lax Online Meeting";
const SECTION_HEADINGS = [OUTCOMES_HEADING, "Meeting details", MATERIAL_HEADING] as const;

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
<ul class="workshop-highlights" aria-label="Meeting at a glance">
<li><span aria-hidden="true">▣</span> Wed, 7 Oct 2026</li>
<li><span aria-hidden="true">◷</span> 1 pm ET · 10 am PT</li>
<li><span aria-hidden="true">◴</span> 90 minutes</li>
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
<h2 id="workshop-details-heading">Meeting details</h2>
<div class="latex-content">
${markdown.render(section("Meeting details"), "../")}
</div>
</section>
</div>
<section class="workshop-registration" aria-label="Meeting registration">
<div class="workshop-form-frame">
<iframe src="${attr(FORM_URL)}" width="640" height="840" frameborder="0" marginheight="0" marginwidth="0" title="Lax Online Meeting preregistration form">Loading…</iframe>
</div>
</section>
<section class="workshop-panel workshop-material" aria-labelledby="workshop-material-heading">
<p class="workshop-section-number" aria-hidden="true">03</p>
<h2 id="workshop-material-heading">${esc(MATERIAL_HEADING)}</h2>
<div class="latex-content">
${markdown.render(section(MATERIAL_HEADING), "../")}
</div>
<div class="workshop-video">
<iframe src="${attr(VIDEO_URL)}" title="Recording of the 1st Lax Online Meeting" loading="lazy" allow="encrypted-media; picture-in-picture; fullscreen" referrerpolicy="strict-origin-when-cross-origin" allowfullscreen></iframe>
</div>
<p class="workshop-material-links"><a href="../assets/${SLIDES_FILE}" download="${SLIDES_FILE}">Download the slides (PDF)</a> · <a href="https://www.youtube.com/watch?v=vx1IRXcA2bg">Watch on YouTube</a></p>
</section>
</article>`;
  return page({
    title: `${copy.title} — Lax Lean Archive`,
    rootRel: "../",
    canonicalPath: "workshop/",
    sidebar: "",
    content,
    detailClass: "detail-workshop",
    frameOrigins: FORM_FRAME_ORIGINS,
  });
}
