/** Canonical URL used in permanent citation links. */
export const DEFAULT_SITE_URL =
  process.env.LAX_SITE_URL ?? "https://laxarchive.org";

/** Hosted Remark42 instance used by submission and concept discussions. */
export const REMARK42_URL =
  process.env.LAX_REMARK42_URL ?? "https://remark42-3-74-72-66.nip.io";

/** Remark42 site namespace. Changing it creates a separate comment archive. */
export const REMARK42_SITE_ID =
  process.env.LAX_REMARK42_SITE_ID ?? "remark";

/** The proof package corresponding to LaxN is always named LaxNProofs. */
export const PROOF_SUFFIX = "Proofs";
