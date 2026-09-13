import { pathData, quantizeGeometry, samePoint, simplifyCollinear } from "./geometry.js";
import type { GraphGeometry, MeasuredGraph, PathCommand, Point, ValidationResult } from "./types.js";
import { parsePathData, validateGeometry } from "./validate.js";

/** Round only true corners, clamping each cut to half its incident segment
 * and preserving a 10px normal stub at each semantic endpoint. */
export function terminalSafeCorners(input: readonly Point[], radius: number, terminalLength = 10): PathCommand[] {
  const points = simplifyCollinear(input);
  if (!points.length) return [];
  const out: PathCommand[] = [{ kind: "M", p: points[0]! }];
  for (let i = 1; i + 1 < points.length; i++) {
    const a = points[i - 1]!, b = points[i]!, c = points[i + 1]!;
    const ab = Math.hypot(b.x - a.x, b.y - a.y), bc = Math.hypot(c.x - b.x, c.y - b.y);
    const cross = (b.x - a.x) * (c.y - b.y) - (b.y - a.y) * (c.x - b.x);
    const r = Math.max(0, Math.min(radius, ab / 2, bc / 2, i === 1 ? ab - terminalLength : Infinity, i + 2 === points.length ? bc - terminalLength : Infinity));
    if (r < 0.001 || Math.abs(cross) < 1e-8) { out.push({ kind: "L", p: b }); continue; }
    const before = { x: b.x + (a.x - b.x) * r / ab, y: b.y + (a.y - b.y) * r / ab };
    const after = { x: b.x + (c.x - b.x) * r / bc, y: b.y + (c.y - b.y) * r / bc };
    if (!samePoint(out.at(-1)!.p, before)) out.push({ kind: "L", p: before });
    out.push({ kind: "Q", control: b, p: after });
  }
  if (points.length > 1) out.push({ kind: "L", p: points.at(-1)! });
  return out;
}

export type Refinement = Readonly<{ geometry: GraphGeometry; validation: ValidationResult; rounded: boolean; attempts: number }>;
export function validatedRounding(graph: MeasuredGraph, baseline: GraphGeometry, radius = 4): Refinement {
  const original = validateGeometry(graph, baseline);
  if (!original.valid) return { geometry: baseline, validation: original, rounded: false, attempts: 0 };
  let attempts = 0;
  for (const scale of [1, 0.5, 0.25]) {
    attempts++;
    // Serialize and parse BEFORE validation: published precision is the geometry
    // under test. Curve flattening and clearance padding belong to validator.
    const geometry = quantizeGeometry({ ...baseline, edges: baseline.edges.map((edge) => ({ ...edge, sections: edge.sections.map((section) => ({ ...section,
      commands: parsePathData(pathData(terminalSafeCorners(section.points, radius * scale))) })) })) });
    const validation = validateGeometry(graph, geometry);
    if (validation.valid && validation.metrics.crossings <= original.metrics.crossings && validation.metrics.repeatedCrossingPairs <= original.metrics.repeatedCrossingPairs
      && validation.metrics.tangencies <= original.metrics.tangencies)
      return { geometry, validation, rounded: geometry.edges.some((e) => e.sections.some((s) => s.commands?.some((c) => c.kind === "Q"))), attempts };
  }
  return { geometry: baseline, validation: original, rounded: false, attempts };
}
