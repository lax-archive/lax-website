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
<section class="page-reactions" aria-labelledby="page-reactions-title" data-reactions-host="${attr(REMARK42_URL)}" data-reactions-url="${attr(threadUrl)}">
<div class="page-reactions-heading">
<div>
<p class="discussion-eyebrow">Reader response</p>
<h3 class="section-title" id="page-reactions-title">Was this page useful?</h3>
<p>Like or dislike this submission or concept. Votes and voter names are public.</p>
</div>
<p class="page-reactions-status" data-reactions-status role="status">Loading responses…</p>
</div>
<div class="page-reactions-actions" aria-label="Page rating">
<button class="page-reaction-button page-reaction-like" type="button" data-reaction-vote="1" aria-pressed="false" disabled><span class="page-reaction-icon" aria-hidden="true">↑</span><span>Like</span><strong data-reaction-count="1">0</strong></button>
<button class="page-reaction-button page-reaction-dislike" type="button" data-reaction-vote="-1" aria-pressed="false" disabled><span class="page-reaction-icon" aria-hidden="true">↓</span><span>Dislike</span><strong data-reaction-count="-1">0</strong></button>
</div>
<div class="page-reactions-voters" aria-live="polite">
<details data-reaction-voters="1" hidden><summary>People who liked this</summary><ul></ul></details>
<details data-reaction-voters="-1" hidden><summary>People who disliked this</summary><ul></ul></details>
</div>
<p class="page-reactions-auth">Voting requires ORCID sign-in and a public name on your ORCID record. <a data-reactions-login href="${attr(`${REMARK42_URL.replace(/\/+$/, "")}/auth/orcid/login?site=${encodeURIComponent(REMARK42_SITE_ID)}&from=${encodeURIComponent(threadUrl)}`)}">Sign in with ORCID</a></p>
</section>
<div class="discussion-heading">
<div class="discussion-heading-copy">
<p class="discussion-eyebrow">Community review</p>
<h3 class="section-title" id="discussion-title">Discussion</h3>
<p>Ask a question, suggest a correction, or add context. Sign in with ORCID to comment and vote; your ORCID profile must share a public name.</p>
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
