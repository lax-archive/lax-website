import { contentMarkdown } from "../content.js";
import { attr, page } from "../html.js";
import type { PageContext } from "./shared.js";
import { proofFlipDemo } from "./proof-flip.js";
import { setupTabs } from "./setup-tabs.js";

/** Render a repository-owned editorial Markdown page. */
export async function contentPage(
  { markdown }: PageContext,
  name: string,
  title: string,
): Promise<string> {
  const source = contentMarkdown(`${name}.md`)
    .replace(/^#\s+.*(?:\r?\n)+/, "");
  let body: string;
  let scripts: string[] = [];
  if (name === "about") {
    const sections = source.split(/^\{\{concept-proof-flip\}\}$/m);
    const hasProofFlip = sections.length > 1;
    body = sections.map((section) => markdown.render(section, ""))
      .join(hasProofFlip ? await proofFlipDemo() : "");
    if (hasProofFlip) scripts = ["assets/proof-flip.js"];
  } else if (name === "contributing") {
    const sections = source.split(/^\{\{setup-tabs\}\}$/m);
    if (sections.length !== 2) throw new Error("contributing.md must contain one {{setup-tabs}} marker");
    body = `${markdown.render(sections[0]!, "")}
${setupTabs(contentMarkdown("setup.md"), markdown, "", { idPrefix: "getting-started-setup", contentPage: true })}
${markdown.render(sections[1]!, "")}`;
    scripts = ["assets/setup-tabs.js"];
  } else {
    body = markdown.render(source, "");
  }
  const sidebar = `<a class="sidebar-back" href="index.html"><span class="sidebar-back-arrow" aria-hidden="true">←</span>Archive</a>
<ul id="entry-list">
<li class="active"><a class="entry-link" href="${name}.html" data-full-title="${attr(title)}"><span class="entry-label"><span class="entry-label-text">${title}</span></span></a></li>
</ul>`;
  const content = `<header class="paper-head">
<h1 class="paper-title">${title}</h1>
</header>
<article class="content-page latex-content">
${body}
</article>`;
  return page({ title: `${title} — Lax Lean Archive`, rootRel: "", canonicalPath: `${name}.html`, sidebar, content,
    scripts });
}
