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
