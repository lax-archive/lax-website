import { REMARK42_IDENTITY_URL, REMARK42_SITE_ID, REMARK42_URL } from "../../config.js";
import { attr, page } from "../html.js";
import type { PageContext } from "./shared.js";

/** Direct-only public activity stream. Deliberately omitted from site navigation. */
export function allCommentsPage(_ctx: PageContext): string {
  const sidebar = `<a class="sidebar-back" href="../index.html"><span class="sidebar-back-arrow" aria-hidden="true">←</span>Archive</a>`;
  const content = `<header class="paper-head">
<p class="activity-eyebrow">Community activity</p>
<h1 class="paper-title">All comments</h1>
<p class="activity-lede">The newest public discussion across archive submissions and concepts.</p>
</header>
<section class="activity-stream" id="all-comments" aria-labelledby="activity-heading" aria-busy="true" data-remark42-host="${attr(REMARK42_URL)}" data-remark42-site="${attr(REMARK42_SITE_ID)}" data-identity-url="${attr(REMARK42_IDENTITY_URL)}">
<h2 class="visually-hidden" id="activity-heading">Comment activity</h2>
<p class="activity-status" data-activity-status role="status">Loading comments…</p>
<ol class="activity-list" data-activity-list></ol>
<button class="activity-more" data-activity-more type="button" hidden>Load more comments</button>
<noscript><p class="activity-status">Enable JavaScript to load the public comment activity.</p></noscript>
</section>`;
  return page({
    title: "All comments — Lax Lean Archive",
    rootRel: "../",
    sidebar,
    content,
    scripts: ["assets/all-comments.js"],
  });
}
