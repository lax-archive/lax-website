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
export const EPOCH = "v4.33.0";

/** The content spec an environment's records follow. */
export type EnvironmentSpecVersion = 1 | 2;

/**
 * The spec version of each environment the archive has admitted, as the CLI's
 * environment table (`environments.ts` in the `lax` repository) records it:
 * what a statement and a proof *are* in that environment. A record's own
 * `manifest.specVersion` is the authority for every environment the archive
 * holds work in — the publisher holds it to the row — so this table matters
 * only for an environment without records, which is the epoch listed at zero
 * in `environments.json` right after its bump. Edited at each admission that
 * changes the spec; the rule below covers a row this file has not caught up
 * with: spec 2 begins with the `v4.35.0` environment (`axiomfree-plan.md`,
 * stage 6).
 */
export const ENVIRONMENT_SPEC_VERSIONS: Readonly<Record<string, EnvironmentSpecVersion>> = {
  "v4.30.0": 1,
  "v4.33.0": 1,
  "v4.35.0": 2,
};

const FIRST_SPEC_2_ENVIRONMENT = [4, 35, 0];

/** The spec version of an environment this site holds no record in. */
export function environmentSpecVersion(environment: string): EnvironmentSpecVersion {
  const known = ENVIRONMENT_SPEC_VERSIONS[environment];
  if (known !== undefined) return known;
  const parts = (environment.match(/\d+/g) ?? []).map(Number);
  for (let i = 0; i < FIRST_SPEC_2_ENVIRONMENT.length; i += 1) {
    const difference = (parts[i] ?? -1) - FIRST_SPEC_2_ENVIRONMENT[i]!;
    if (difference !== 0) return difference > 0 ? 2 : 1;
  }
  return 2;
}
