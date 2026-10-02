import { page } from "../html.js";
import { submissionLibrary } from "./submission-library.js";
import type { PageContext } from "./shared.js";

/** The archive library on its own stable URL, without the landing page's
 * introduction, examples, proof network, setup guide, foundations, or FAQ. */
export function submissionsPage(ctx: PageContext): string {
  const heading = "submissions-page-heading";
  const content = `<header class="submissions-page-head">
<p class="submissions-page-eyebrow">Archive library</p>
<h1 class="submissions-page-title" id="${heading}">Submissions</h1>
<p class="submissions-page-intro">Browse, search, and filter the archive’s current submissions.</p>
</header>
${submissionLibrary(ctx, {
    rootRel: "../",
    labelledBy: heading,
    id: "submissions-library",
    standalone: true,
  })}`;
  return page({
    title: "Submissions — Lax Lean Archive",
    rootRel: "../",
    canonicalPath: "submissions/",
    sidebar: "",
    content,
    detailClass: "detail-submissions",
    landingHeader: true,
  });
}
