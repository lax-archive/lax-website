/** Canonical URL used in permanent citation links. */
export const DEFAULT_SITE_URL =
  process.env.LAX_SITE_URL ?? "https://laxarchive.org";

/** Hosted Remark42 instance used by submission and concept discussions. */
export const REMARK42_URL =
  process.env.LAX_REMARK42_URL ?? "https://comments.laxarchive.org";

/** Remark42 site namespace. Changing it creates a separate comment archive. */
export const REMARK42_SITE_ID =
  process.env.LAX_REMARK42_SITE_ID ?? "remark";

/**
 * Public identity bridge for resolving Remark42's privacy-preserving user hash
 * to the ORCID iD and current public name validated during authentication.
 */
export const REMARK42_IDENTITY_URL =
  process.env.LAX_REMARK42_IDENTITY_URL ?? `${REMARK42_URL.replace(/\/+$/, "")}/reactions/v1/identity`;

/** The proof package corresponding to LaxN is always named LaxNProofs. */
export const PROOF_SUFFIX = "Proofs";

/**
 * The archive's **epoch**: the environment — a Lean toolchain and the mathlib
 * release tag it builds, named by the Lean version string — that this year's
 * submissions are recommended to be written in. A record in any other
 * admitted environment is equally valid and equally permanent, but only
 * submissions sharing its environment can cite it, so its pages say so.
 *
 * Edited once a year, at the epoch bump (step 3 of the runbook in
 * `environments-plan.md` in the `lax` repository, beside the CLI's own
 * environment table). `generateSite`'s third argument overrides it, so
 * `lax serve` shows the epoch the *installed CLI's* table names rather than
 * whatever this file said when the renderer was released.
 */
export const EPOCH = "v4.30.0";
