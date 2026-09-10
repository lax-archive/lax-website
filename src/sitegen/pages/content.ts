import { contentMarkdown } from "../content.js";
import { attr, page } from "../html.js";
import type { PageContext } from "./shared.js";

/** Render a repository-owned editorial Markdown page. */
export function contentPage(
  { markdown }: PageContext,
  name: string,
  title: string,
  options: { /** a warning above the text, e.g. that the page is a placeholder */ warning?: string } = {},
): string {
  const source = contentMarkdown(`${name}.md`)
    .replace(/^#\s+.*(?:\r?\n)+/, "");
  const sidebar = `<a class="sidebar-back" href="index.html"><span class="sidebar-back-arrow" aria-hidden="true">←</span>Archive</a>
<ul id="entry-list">
<li class="active"><a class="entry-link" href="${name}.html" data-full-title="${attr(title)}"><span class="entry-label"><span class="entry-label-text">${title}</span></span></a></li>
</ul>`;
  const warning = options.warning ? `<p class="content-warning" role="note">${options.warning}</p>
` : "";
  const content = `<header class="paper-head">
<h1 class="paper-title">${title}</h1>
</header>
${warning}<article class="content-page latex-content">
${markdown.render(source, "")}
</article>`;
  return page({ title: `${title} — Lax Lean Archive`, rootRel: "", sidebar, content });
}
