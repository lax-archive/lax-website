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
<p>Ask a question, suggest a correction, or add context. Sign in with ORCID to comment and react; your ORCID profile must share a public name.</p>
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

/** Compact page-level rating placed beside the page's primary metadata. */
export function pageReactions(pathname: string): string {
  const threadUrl = canonicalThreadUrl(pathname);
  const loginUrl = `${REMARK42_URL.replace(/\/+$/, "")}/auth/orcid/login?site=${encodeURIComponent(REMARK42_SITE_ID)}&from=${encodeURIComponent(threadUrl)}`;
  const control = (reaction: "like" | "dislike" | "rocket", label: string, icon: string, noun: string) => {
    const id = `page-reaction-voters-${reaction}`;
    return `<div class="page-reaction-control">
<button class="page-reaction-button" type="button" data-reaction="${reaction}" aria-pressed="false"><span class="page-reaction-icon" aria-hidden="true">${icon}</span><span>${label}</span></button>
<button class="page-reaction-voters" type="button" data-reaction-voters="${reaction}" aria-expanded="false" aria-controls="${id}"><strong data-reaction-count="${reaction}">0</strong><span class="visually-hidden">Show people who ${noun} this page</span></button>
<div class="page-reaction-voters-popover" id="${id}" data-reaction-voters-popover="${reaction}" hidden><p data-reaction-empty>No public ${noun}s yet.</p><ul></ul></div>
</div>`;
  };
  return `<section class="page-reactions" aria-label="Page rating" data-reactions-host="${attr(REMARK42_URL)}" data-reactions-url="${attr(threadUrl)}">
<div class="page-reactions-actions">
${control("like", "Like", "👍", "like")}
${control("dislike", "Dislike", "👎", "dislike")}
${control("rocket", "Rocket", "🚀", "rocket")}
</div>
<p class="visually-hidden" data-reactions-status role="status">Loading page rating…</p>
<a class="visually-hidden" data-reactions-login href="${attr(loginUrl)}">Sign in with ORCID</a>
<noscript><p class="page-reactions-noscript"><a href="${attr(loginUrl)}">Sign in with ORCID</a> to rate this page.</p></noscript>
</section>`;
}
