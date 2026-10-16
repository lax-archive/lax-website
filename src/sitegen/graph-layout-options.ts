import type { LayoutOptions } from "../graph-layout/portfolio.js";
import type { LayoutProfile } from "../graph-layout/types.js";
import type { DisplayGraph } from "./graph-project.js";

/** Popup diagrams have their own placement and routing search. They can
 * spend space to remove crossings and wrap independent proof components. */
export function graphLayoutOptions(display: DisplayGraph, profile: LayoutProfile): Omit<LayoutOptions, "inputDigest"> {
  if (!display.proofDetail) return { profile };
  return { componentPacking: "compact", optimizeCrossings: true,
    profile: { ...profile, id: `${profile.id}:local-proofs-v1`,
      sweeps: Math.max(profile.sweeps, 16), candidates: Math.max(profile.candidates, 48) } };
}
