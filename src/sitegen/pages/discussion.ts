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
<p>Ask a question or add context. Endorsements and structured flags are kept in the review panel above; your ORCID profile must share a public name.</p>
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

interface PageReviewOptions {
  kind?: "submission" | "concept";
  sourceLines?: number;
}

/** Compact page-level review controls placed beside the primary metadata. */
export function pageReactions(pathname: string, options: PageReviewOptions = {}): string {
  const threadUrl = canonicalThreadUrl(pathname);
  const loginUrl = `${REMARK42_URL.replace(/\/+$/, "")}/auth/orcid/login?site=${encodeURIComponent(REMARK42_SITE_ID)}&from=${encodeURIComponent(threadUrl)}`;
  const kind = options.kind ?? "submission";
  const sourceLines = kind === "concept" ? Math.max(0, options.sourceLines ?? 0) : 0;
  const target = kind === "concept" ? "concept" : "submission";
  return `<section class="page-reactions" aria-label="Community review" data-reactions-host="${attr(REMARK42_URL)}" data-reactions-url="${attr(threadUrl)}" data-review-kind="${kind}" data-source-lines="${sourceLines}">
<div class="page-reactions-actions">
<div class="page-reaction-control">
<button class="page-reaction-button" type="button" data-reaction="endorse" aria-pressed="false" title="Say that this ${target} is correct"><span class="page-reaction-icon" aria-hidden="true">✅</span><span>Endorse</span></button>
<button class="page-reaction-voters" type="button" data-reaction-voters="endorse" aria-expanded="false" aria-controls="page-reaction-voters-endorse"><strong data-reaction-count="endorse">0</strong><span class="visually-hidden">Show people who endorse this ${target}</span></button>
<div class="page-reaction-voters-popover" id="page-reaction-voters-endorse" data-reaction-voters-popover="endorse" hidden><p data-reaction-empty>No public endorsements yet.</p><ul></ul></div>
</div>
<div class="page-reaction-control page-flag-control">
<button class="page-reaction-button" type="button" data-reaction="flag" aria-pressed="false" aria-haspopup="dialog" title="Explain why this ${target} may be false"><span class="page-reaction-icon" aria-hidden="true">🚩</span><span>Flag</span></button>
<button class="page-reaction-voters" type="button" data-flag-list-open aria-haspopup="dialog" aria-controls="page-flag-list"><strong data-reaction-count="flag">0</strong><span class="visually-hidden">Show flags for this ${target}</span></button>
</div>
</div>
<p class="page-reactions-status" data-reactions-status role="status">Loading review…</p>
<a class="visually-hidden" data-reactions-login href="${attr(loginUrl)}">Sign in with ORCID</a>
<dialog class="review-dialog flag-list-dialog" id="page-flag-list" data-flag-list-dialog aria-labelledby="page-flag-list-title">
<div class="review-dialog-header"><div><p class="discussion-eyebrow">Community review</p><h2 id="page-flag-list-title">Flags</h2></div><button class="review-dialog-close" type="button" data-flag-list-close aria-label="Close flags">×</button></div>
<p class="review-dialog-intro">Each flag is tied to a public ORCID identity and explains why this ${target} may be incorrect.</p>
<p data-flag-list-empty>No flags have been submitted.</p><ol class="flag-list" data-flag-list></ol>
</dialog>
<dialog class="review-dialog flag-editor-dialog" id="page-flag-editor" data-flag-editor aria-labelledby="page-flag-editor-title">
<form data-flag-form>
<div class="review-dialog-header"><div><p class="discussion-eyebrow">Community review</p><h2 id="page-flag-editor-title">Flag this ${target}</h2></div><button class="review-dialog-close" type="button" data-flag-cancel aria-label="Close flag form">×</button></div>
<p class="review-dialog-intro">State precisely what appears incorrect. This explanation will be public under your ORCID name.</p>
<label class="flag-message-label" for="page-flag-message">What is wrong?</label>
<textarea id="page-flag-message" data-flag-message rows="6" maxlength="2000" required placeholder="Describe the incorrect claim, missing assumption, or counterexample."></textarea>
${sourceLines ? `<div class="flag-line-fields"><input type="hidden" data-flag-line><button class="secondary-button" type="button" data-flag-line-picker>Choose from source</button><p class="flag-line-selection" data-flag-line-selection aria-live="polite">No source line selected.</p></div>` : ""}
<p class="flag-form-status" data-flag-form-status role="status"></p>
<div class="review-dialog-actions"><button class="danger-button" type="button" data-flag-remove hidden>Remove my flag</button><span></span><button class="secondary-button" type="button" data-flag-cancel>Cancel</button><button class="primary-button" type="submit">Publish flag</button></div>
</form>
</dialog>
<noscript><p class="page-reactions-noscript"><a href="${attr(loginUrl)}">Sign in with ORCID</a> to review this page.</p></noscript>
</section>`;
}
