import { attr, esc, page, plural } from "../html.js";
import type { LocatedProof } from "../model.js";
import {
  draftBanner,
  githubSource,
  versionHistoryPanel,
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
  const conclusion = ctx.model.statementHome.get(proof.conclusion);
  if (!conclusion)
    throw new Error(`statement ${proof.conclusion} has no home concept in the archive`);
  const proven = ctx.model.network.proven;
  const outstanding = proof.assumptions.filter((id) => !proven.has(id));
  const groundedHelp = "No open assumptions remain in the archive: every dependency is backed by a checked proof, ultimately reducing to Lean and Mathlib.";
  const pill = outstanding.length === 0
    ? `<span class="status-pill pill-proven" tabindex="0" data-tooltip="${attr(groundedHelp)}" aria-label="Grounded. ${attr(groundedHelp)}">grounded</span>`
    : `<span class="status-pill pill-partial" title="The relationship is checked, but ${plural(outstanding.length, "assumption is", "assumptions are")} still open.">conditional — ${plural(outstanding.length, "open assumption")}</span>`;

  const source = submission.record.source;
  const githubFile = source
    ? githubSource(source.repository, source.commit, source.folder, proof.path)
    : undefined;

  const sections = (proof.sections ?? [])
    .map((s) => `<div class="block"><h3>${ctx.markdown.renderAuthorInline(s.title, "../")}</h3><div class="latex-content">${ctx.markdown.renderAuthorProse(s.markdown, "../")}</div></div>`)
    .join("\n");
  const pathLink = githubFile
    ? `<a href="${attr(githubFile)}"><code>${esc(proof.path)}</code></a>`
    : `<code>${esc(proof.path)}</code>`;

  const content = `${versionHistoryPanel(ctx, submission.record.id, "../")}${draftBanner(submission.record.state)}
<div class="detail-heading concept-heading proof-heading">
<div class="proof-heading-content"><h1 class="concept-title">Proof of <span class="proof-concept-title">\`${ctx.markdown.renderAuthorInline(conclusion.concept.title, "../")}\`</span></h1>
<p class="concept-microline proof-microline"><span class="status-pills">${pill}</span><span>${pathLink} · <a href="index.html">${esc(output.id)}</a></span></p></div>
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
    scripts: ["assets/version-history.js"],
  });
}
