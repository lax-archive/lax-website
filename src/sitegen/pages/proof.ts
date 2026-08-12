import { esc, page, plural, proofBadge } from "../html.js";
import type { LocatedProof } from "../model.js";
import {
  draftBanner,
  githubSource,
  type PageContext,
  proofJudgment,
  sourceButton,
  submissionSidebar,
} from "./shared.js";

/** The proof page: the judgment card up front, then the annotation body.
 * The Lean proof code itself is deliberately not displayed — the page shows
 * the checked relationship and where it comes from. */
export function proofPage(ctx: PageContext, located: LocatedProof): string {
  const { submission, output, proof } = located;
  const proven = ctx.model.network.proven;
  const outstanding = proof.assumptions.filter((id) => !proven.has(id));
  const pill = outstanding.length === 0
    ? `<span class="status-pill pill-proven" title="Every assumption is itself proven; the conclusion stands unconditionally.">grounded</span>`
    : `<span class="status-pill pill-partial" title="The relationship is checked, but ${plural(outstanding.length, "assumption is", "assumptions are")} still open.">conditional — ${plural(outstanding.length, "open assumption")}</span>`;

  const source = submission.record.source;
  const githubFile = source
    ? githubSource(source.repository, source.commit, source.folder, proof.path)
    : undefined;

  const sections = (proof.sections ?? [])
    .map((s) => `<div class="block"><h3>${ctx.markdown.renderAuthorInline(s.title, "../")}</h3><div class="latex-content">${ctx.markdown.renderAuthorProse(s.markdown, "../")}</div></div>`)
    .join("\n");

  const content = `${draftBanner(submission.record.state)}
<div class="detail-heading concept-heading">
<div><p class="concept-id">${proofBadge()}<code>${esc(proof.id)}</code></p>
<p class="concept-microline"><code>${esc(proof.path)}</code> · <a href="index.html">${esc(output.id)}</a></p></div>
<span class="status-pills">${pill}</span>
</div>
<div class="block block-evidence"><h3>What this proof establishes</h3>
${proofJudgment(ctx.model, proof, "../", output.id)}
<p class="honesty-note">Assuming the claims on the left, the claim on the right holds — checked by the archive's pipeline. Proof code is not displayed here.</p>
${githubFile ? `<p class="source-action">${sourceButton(githubFile, "Read the Lean proof on GitHub")}</p>` : ""}
</div>
${proof.description.trim() ? `<div class="block block-statement"><h3>Description</h3><div class="latex-content">${ctx.markdown.renderAuthorProse(proof.description, "../")}</div></div>` : ""}
${sections}`;

  return page({
    title: `${proof.id} — ${output.id}`,
    rootRel: "../",
    sidebar: submissionSidebar(ctx.model, submission, "../", { activeId: proof.id }),
    content,
  });
}
