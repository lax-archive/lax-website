import { indexedGraph, stronglyConnectedComponents, weakComponents } from "./components.js";
import { quantize, quantizeGeometry } from "./geometry.js";
import { layoutGroups } from "./groups.js";
import { canonicalJson, compareText, deepFreeze, normalizeGraph } from "./normalize.js";
import { emptyStatistics, layoutDag, type CandidateReport, type LayoutOptions, type LayoutResult, type LayoutStatistics } from "./portfolio.js";
import { DEFAULT_PROFILE, ENGINE_VERSION, GEOMETRY_SCHEMA_VERSION, GraphDiagnosticError, type Diagnostic, type GraphGeometry, type MeasuredGraph, type Point } from "./types.js";
import { validateGeometry } from "./validate.js";
import { nondominated } from "./score.js";

export type { LayoutOptions, LayoutResult, LayoutStatistics } from "./portfolio.js";
export { DEFAULT_PROFILE, ENGINE_VERSION, GEOMETRY_SCHEMA_VERSION } from "./types.js";
export { SELECTION_POLICY } from "./score.js";

/** Translation is the only operation performed during component packing.
 * Nodes, ports, sections, curves and group gates move as one complete object. */
export function translateGeometry(geometry: GraphGeometry, dx: number, dy: number): GraphGeometry {
  const point = (p: Point) => ({ x: p.x + dx, y: p.y + dy });
  return { ...geometry, bounds: { ...geometry.bounds, ...point(geometry.bounds) },
    nodes: geometry.nodes.map((n) => ({ ...n, ...point(n) })), ports: geometry.ports.map((p) => ({ ...p, ...point(p) })),
    groups: geometry.groups?.map((g) => ({ ...g, ...point(g), ...(g.gates ? { gates: g.gates.map((gate) => ({ ...gate, point: point(gate.point) })) } : {}) })),
    edges: geometry.edges.map((e) => ({ ...e, sections: e.sections.map((s) => ({ ...s, points: s.points.map(point),
      ...(s.commands ? { commands: s.commands.map((c) => c.kind === "Q" ? { ...c, p: point(c.p), control: point(c.control) } : { ...c, p: point(c.p) }) } : {}) })) })) };
}
function addStatistics(total: LayoutStatistics, part: LayoutStatistics): void {
  for (const key of Object.keys(total) as (keyof LayoutStatistics)[])
    total[key] = key === "ranks" || key === "maximumRankWidth" ? Math.max(total[key], part[key]) : total[key] + part[key];
}

/** Pure deterministic archive/local entry point. Every weak component owns
 * its full operation budgets, making component interiors independent of
 * unrelated isolated additions. There is no browser or host dependency. */
export function layoutGraph(input: MeasuredGraph, options: LayoutOptions): LayoutResult {
  const graph = normalizeGraph(input), profile = options.profile ?? DEFAULT_PROFILE;
  const indexed = indexedGraph(graph), components = weakComponents(indexed.nodeCount, indexed.edges);
  const parts: GraphGeometry[] = [], alternatives: { component: number; id: string; geometry: GraphGeometry }[] = [];
  const diagnostics: Diagnostic[] = [], candidates: CandidateReport[] = [], stats = emptyStatistics();
  for (const members of components) {
    const nodeIds = new Set(members.map((i) => graph.nodes[i]!.id));
    const nodes = graph.nodes.filter((n) => nodeIds.has(n.id)), ports = new Set(nodes.flatMap((n) => n.ports.map((p) => p.id)));
    const component: MeasuredGraph = { nodes, edges: graph.edges.filter((e) => ports.has(e.sourcePortId)) };
    const data = indexedGraph(component), sccs = stronglyConnectedComponents(data.nodeCount, data.edges);
    const cyclic = sccs.some((c) => c.length > 1) || data.edges.some((e) => e.source === e.target);
    if (cyclic) {
      const geometry = layoutGroups(component, (outer) => {
        const result = layoutDag(outer, options); addStatistics(stats, result.stats); diagnostics.push(...result.diagnostics); candidates.push(...result.candidates);
        return result.geometry;
      }, options.inputDigest, profile);
      const checked = validateGeometry(component, geometry);
      if (!checked.valid) throw new GraphDiagnosticError(checked.diagnostics);
      parts.push(geometry);
    } else {
      const result = layoutDag(component, options); parts.push(result.geometry); addStatistics(stats, result.stats);
      diagnostics.push(...result.diagnostics); candidates.push(...result.candidates);
      for (const candidate of result.candidateGeometries ?? []) alternatives.push({ component: parts.length - 1,
        id: `${nodes[0]!.id}:${candidate.id}`, geometry: candidate.geometry });
    }
  }
  // Put independent components beside one another, with their main results
  // aligned at the top. Never wrap components into additional graph rows.
  const pack = (parts: readonly GraphGeometry[]): GraphGeometry => {
  const gap = profile.nodeGap;
  const placed: GraphGeometry[] = []; let x = 0, height = 0, width = 0;
  for (const part of parts) {
    placed.push(translateGeometry(part, x - part.bounds.x, -part.bounds.y));
    height = Math.max(height, part.bounds.height); width = x + part.bounds.width; x += part.bounds.width + gap;
  }
  // Whole-unit outer extents make a 100% SVG viewport match its viewBox
  // exactly. Fractional CSS viewport rounding otherwise perturbs glyph
  // metrics even though the published text coordinates have not changed.
  // Only empty space at the right/bottom grows; all interior geometry keeps
  // its 0.001-unit precision and every component's original translation.
  return quantizeGeometry({ schemaVersion: GEOMETRY_SCHEMA_VERSION, engineVersion: ENGINE_VERSION,
    profileId: profile.id, inputDigest: options.inputDigest,
    bounds: { x: 0, y: 0, width: Math.ceil(quantize(width)), height: Math.ceil(quantize(height)) },
    nodes: placed.flatMap((p) => p.nodes).sort((a, b) => compareText(a.id, b.id)),
    ports: placed.flatMap((p) => p.ports).sort((a, b) => compareText(a.id, b.id)),
    edges: placed.flatMap((p) => p.edges).sort((a, b) => compareText(a.id, b.id)),
    ...(placed.some((p) => p.groups?.length) ? { groups: placed.flatMap((p) => p.groups ?? []).sort((a, b) => compareText(a.id, b.id)) } : {}) });
  };
  const geometry = pack(parts);
  const checked = validateGeometry(graph, geometry);
  if (!checked.valid) throw new GraphDiagnosticError(checked.diagnostics);
  if (geometry.bounds.width > 960 || geometry.bounds.height > 720) diagnostics.push({
    code: "readability-overflow", message: "The complete measured drawing exceeds the preferred viewport; retain readable labels and use scrolling/pan/zoom without dropping incidences.",
  });
  stats.components = components.length;
  const review = [{ id: "selected", geometry, metrics: checked.metrics }];
  const reviewKeys = new Set(options.retainCandidates ? [canonicalJson(geometry)] : []);
  if (options.retainCandidates) for (const alternative of alternatives.slice(0, Math.max(0, profile.candidates - 1))) {
    // Bounded one-component substitutions, never a Cartesian product. Repack
    // complete components and validate the entire drawing for review.
    const replaced = parts.map((part, i) => i === alternative.component ? alternative.geometry : part);
    const candidate = pack(replaced), key = canonicalJson(candidate);
    if (reviewKeys.has(key)) continue;
    reviewKeys.add(key);
    const validation = validateGeometry(graph, candidate);
    if (validation.valid) review.push({ id: alternative.id, geometry: candidate, metrics: validation.metrics });
  }
  return { geometry: deepFreeze(geometry), diagnostics, metrics: checked.metrics, stats, candidates,
    ...(options.retainCandidates ? { candidateGeometries: nondominated(review) } : {}) };
}
