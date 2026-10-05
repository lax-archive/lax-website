import { attr, esc, page, plural, entryPath } from "../html.js";
import type { LocatedProof } from "../model.js";
import { inPaperBlock } from "./paper.js";
import {
  annotationSections,
  certifiedMark,
  PENDING_LABEL,
  draftBanner,
  environmentNotice,
  versionHistoryPanel,
  repositorySource,
  type PageContext,
  proofJudgment,
  rerunCommands,
  statementOrdinal,
  sourceButton,
  sourceProviderName,
  submissionSidebar,
  withheldSourceButton,
} from "./shared.js";

/** The proof page: the judgment card up front, then the annotation body.
 * The Lean proof code itself is deliberately not displayed — the page shows
 * the checked relationship and where it comes from. */
export function proofPage(ctx: PageContext, located: LocatedProof): string {
  const { submission, output, proof } = located;
  const conclusion = ctx.model.statementHome.get(proof.conclusion);
  if (!conclusion)
    throw new Error(`statement ${proof.conclusion} has no home concept in the archive`);
  // A concept declaring several statements: say which of them this proof
  // concludes, by its anonymous position.
  const position = statementOrdinal(ctx.model, proof.conclusion);
  const proven = ctx.model.network.proven;
  const outstanding = proof.assumptions.filter((id) => !proven.has(id));
  const groundedHelp = "No open assumptions remain in the archive: every dependency is backed by a checked proof, ultimately reducing to Lean and Mathlib.";
  // A pending edge (lax decision 12) is stated, not proven: no grounded or
  // conditional status, no certified mark, and an honest note saying so.
  const pill = proof.pending
    ? `<span class="status-pill pill-none" title="The edge's type is stated; its proof contains sorry.">${esc(PENDING_LABEL)}</span>`
    : outstanding.length === 0
    ? `<span class="status-pill pill-proven" tabindex="0" data-tooltip="${attr(groundedHelp)}" aria-label="Grounded. ${attr(groundedHelp)}">grounded</span>`
    : `<span class="status-pill pill-partial" title="The relationship is checked, but ${plural(outstanding.length, "assumption is", "assumptions are")} still open.">conditional — ${plural(outstanding.length, "open assumption")}</span>`;
  // A certified edge: the mark beside the judgment, with the rerun command.
  // The grounded/conditional status above it is composed by this site from
  // the archive's edges and is said so; only the edge itself is certified.
  const certified = proof.pending ? "" : certifiedMark(output, "line");
  const honesty = proof.pending
    ? `<p class="honesty-note">This edge is pending: its type is stated as shown, but its Lean proof contains <code>sorry</code>. It is not in the record's Challenge, is not certified, and proves nothing in the archive until the proof is written. A draft may carry pending edges; registration refuses them.</p>`
    : certified
    ? `<p class="honesty-note">Assuming the hypotheses on the left, in binder order, the claim on the right holds — certified by Lean's <code>lake comparator</code>, which held this proof to the record's Challenge. The grounded or conditional status is composed by this site from the archive's edges. Proof code is not displayed here.</p>`
    : `<p class="honesty-note">Assuming the claims on the left, the claim on the right holds — checked by the archive's pipeline. Proof code is not displayed here.</p>`;

  const anonymous = output.manifest.anonymous === true;
  const source = submission.record.source;
  const sourceFile = source && !anonymous
    ? repositorySource(source.repository, source.commit, source.folder, proof.path)
    : undefined;
  const sourceWithheld = anonymous && Boolean(source);

  const sections = annotationSections(ctx, proof.sections, "../");
  const pathLink = sourceFile
    ? `<a href="${attr(sourceFile)}"><code>${esc(proof.path)}</code></a>`
    : `<code>${esc(proof.path)}</code>`;

  const content = `${versionHistoryPanel(ctx, submission.record.id, "../")}${draftBanner(submission)}${environmentNotice(ctx.model, submission)}
<div class="detail-heading concept-heading proof-heading">
<div class="proof-heading-content"><h1 class="concept-title">Proof of <span class="proof-concept-title">\`${ctx.markdown.renderAuthorInline(conclusion.concept.title, "../")}\`</span>${position ? ` <span class="claim-ordinal">(${esc(position.label)})</span>` : ""}</h1>
<p class="concept-microline proof-microline"><span class="status-pills">${pill}</span><span>${pathLink} · <a href="index.html">${esc(output.id)}</a></span></p></div>
</div>
<div class="block block-evidence"><h3>What this proof establishes</h3>
${proofJudgment(ctx.model, proof, "../", output.id)}
${certified ? `${certified}\n${rerunCommands(submission.record.id)}\n` : ""}${honesty}
${sourceFile
    ? `<p class="source-action">${sourceButton(sourceFile, `Read the Lean proof on ${sourceProviderName(sourceFile)}`)}</p>`
    : sourceWithheld
      ? `<p class="source-action">${withheldSourceButton()}</p>`
      : ""}
</div>
${inPaperBlock(ctx, proof.id, output.id, "../")}
${proof.description.trim() ? `<div class="block block-statement"><h3>Description</h3><div class="latex-content">${ctx.markdown.renderAuthorProse(proof.description, "../")}</div></div>` : ""}
${sections}`;

  return page({
    title: `${proof.id} — ${output.id}`,
    rootRel: "../",
    canonicalPath: entryPath(submission.record.id, proof.id),
    sidebar: submissionSidebar(ctx.model, submission, "../", { activeId: proof.id }),
    sidebarState: "open",
    content,
    noIndex: output.manifest.unlisted === true,
    description: ctx.markdown.plainAuthorTitle(proof.description),
    scripts: ["assets/version-history.js"],
  });
}
