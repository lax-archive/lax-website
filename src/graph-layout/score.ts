import { compareText } from "./normalize.js";
import type { GeometryMetrics } from "./types.js";

/** Policy frozen before corpus evaluation. Extent is a hard eligibility
 * envelope, followed by zero crossing tolerance. Numerical policy changes
 * require a new version and a new tuning/held-out comparison report. */
export const SELECTION_POLICY = "extent-then-crossings-v1";
export interface ScoredCandidate { id: string; metrics: GeometryMetrics }
const area = (m: GeometryMetrics) => m.width * m.height;
export function compareQuality(a: ScoredCandidate, b: ScoredCandidate): number {
  const x = a.metrics, y = b.metrics;
  return x.crossings - y.crossings || x.repeatedCrossingPairs - y.repeatedCrossingPairs
    || x.tangencies - y.tangencies || x.bends - y.bends || x.length - y.length
    || area(x) - area(y) || compareText(a.id, b.id);
}
export function selectCandidate<T extends ScoredCandidate>(candidates: readonly T[]): T {
  if (!candidates.length) throw new Error("Cannot select an empty geometry portfolio");
  const compact = [...candidates].sort((a, b) => area(a.metrics) - area(b.metrics) || compareText(a.id, b.id))[0]!;
  const width = Math.max(960, compact.metrics.width * 1.5), height = Math.max(720, compact.metrics.height * 1.5);
  const maximumArea = Math.max(960 * 720, area(compact.metrics) * 2);
  const eligible = candidates.filter((c) => c.metrics.width <= width && c.metrics.height <= height && area(c.metrics) <= maximumArea);
  return [...eligible].sort(compareQuality)[0]!;
}
export function nondominated<T extends ScoredCandidate>(candidates: readonly T[]): readonly T[] {
  const values = (m: GeometryMetrics) => [m.crossings, m.repeatedCrossingPairs, m.tangencies, m.bends, m.length, m.width, m.height];
  return candidates.filter((c) => !candidates.some((other) => {
    if (other === c) return false;
    const a = values(other.metrics), b = values(c.metrics);
    return a.every((v, i) => v <= b[i]!) && a.some((v, i) => v < b[i]!);
  }));
}
