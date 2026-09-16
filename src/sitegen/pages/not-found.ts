import { page } from "../html.js";

/**
 * The page GitHub Pages serves for an address that does not exist:
 * `/404.html`, at any depth. Most such addresses are records that were
 * deleted — a deleted record is a tombstone with no page (see `SiteModel`)
 * — or links to a page that moved. Asset and navigation links are absolute,
 * because the page is served from wherever the missing address was.
 */
export function notFoundPage(): string {
  const content = `<header class="paper-head">
<h1 class="paper-title">Nothing is here</h1>
</header>
<article class="content-page latex-content">
<p>There is no page at this address.</p>
<p>If you followed a link to a submission, concept, or proof, the record may have been deleted: a deleted record keeps its identifier so that nothing else can take it, but it has no page. A link may also have moved, or have been copied incompletely.</p>
<p><a href="/index.html">Go to the archive</a>, or <a href="/about.html">read about Lax</a>.</p>
</article>`;
  return page({ title: "Page not found — Lax Lean Archive", rootRel: "/", canonicalPath: "404.html", sidebar: "", content, noIndex: true });
}
