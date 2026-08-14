import { DEFAULT_SITE_URL, REMARK42_SITE_ID, REMARK42_URL } from "../../config.js";
import { attr } from "../html.js";

function canonicalThreadUrl(pathname: string): string {
  const base = `${DEFAULT_SITE_URL.replace(/\/+$/, "")}/`;
  return new URL(pathname.replace(/^\/+/, ""), base).toString();
}

/**
 * One canonical Remark42 thread. Thread URLs always point at the production
 * archive so local builds and branch previews share the eventual live
 * discussion instead of creating throwaway copies.
 */
export function discussion(pathname: string): string {
  const threadUrl = canonicalThreadUrl(pathname);
  return `<section class="page-section discussion-section" aria-labelledby="discussion-title">
<div class="discussion-heading">
<div class="discussion-heading-copy">
<p class="discussion-eyebrow">Community review</p>
<h3 class="section-title" id="discussion-title">Discussion</h3>
<p>Ask a question, suggest a correction, or add context. Sign in with ORCID to comment and vote comments up or down.</p>
</div>
<p class="discussion-count"><span class="remark42__counter" data-url="${attr(threadUrl)}">0</span> <span>comments</span></p>
</div>
<div class="discussion-embed-shell">
<p class="discussion-loading" id="remark42-status" role="status"><span class="discussion-loading-mark" aria-hidden="true"></span>Loading discussion…</p>
<div id="remark42" data-remark42-host="${attr(REMARK42_URL)}" data-remark42-site="${attr(REMARK42_SITE_ID)}" data-remark42-url="${attr(threadUrl)}"></div>
</div>
<noscript><p class="discussion-unavailable">Enable JavaScript to read or join the discussion.</p></noscript>
</section>`;
}
