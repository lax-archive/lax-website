import { coordinateCandidates, type CoordinateCandidate } from "./coordinates-bk.js";
import { coordinateL1, horizontalL1 } from "./coordinates-l1.js";
import { placeCorridors, routeProtected, type CorridorPlacement } from "./corridors.js";
import { canonicalJson, compareText } from "./normalize.js";
import { orderGraph } from "./order-heuristic.js";
import { routeOrthogonalCandidates } from "./orthogonal-route.js";
import { makeProperGraph, type Ordering, type ProperGraph } from "./proper-graph.js";
import { rankGraph } from "./rank-simplex.js";
import { validatedRounding } from "./route-refine.js";
import { compareQuality, nondominated, selectCandidate } from "./score.js";
import { DEFAULT_PROFILE, GraphDiagnosticError, type Diagnostic, type GeometryMetrics, type GraphGeometry, type LayoutProfile, type MeasuredGraph } from "./types.js";
import { validateGeometry } from "./validate.js";
import { dummyGaps } from "./order-chain.js";

export interface LayoutOptions {
  inputDigest: string; profile?: LayoutProfile;
  /** Optional host instrumentation. Never included in canonical geometry. */
  onPhase?: (event: { phase: string; start: boolean }) => void;
  /** Development reports can retain validated alternatives. Archive pages
   * only receive the selected geometry. */
  retainCandidates?: boolean;
  /** Local diagrams pack independent components into rows instead of one
   * wide strip; each component still gets an independent layout search. */
  componentPacking?: "compact";
  /** Local diagrams may trade space for fewer crossings. */
  optimizeCrossings?: boolean;
}
export interface CandidateReport { id: string; valid: boolean; metrics: GeometryMetrics; defects: readonly string[]; selected?: boolean; nondominated?: boolean }
export interface LayoutStatistics {
  components: number; ranks: number; maximumRankWidth: number; dummyVertices: number;
  rankPivots: number; rankBudgetExhausted: number; coordinatePivots: number;
  sweeps: number; siftingMoves: number; dpStates: number; routingExpansions: number;
  visibilityVertices: number; candidates: number; chainMoves: number; dummyGaps: number; permutationTrials: number;
  jointSwapTrials: number; jointSwapsAccepted: number; jointSwapBudgetExhausted: number;
}
export interface LayoutResult {
  geometry: GraphGeometry; diagnostics: readonly Diagnostic[]; metrics: GeometryMetrics;
  stats: LayoutStatistics; candidates: readonly CandidateReport[];
  candidateGeometries?: readonly { id: string; geometry: GraphGeometry; metrics: GeometryMetrics }[];
}
export function emptyStatistics(): LayoutStatistics {
  return { components: 0, ranks: 0, maximumRankWidth: 0, dummyVertices: 0, rankPivots: 0,
    rankBudgetExhausted: 0, coordinatePivots: 0, sweeps: 0, siftingMoves: 0, dpStates: 0,
    routingExpansions: 0, visibilityVertices: 0, candidates: 0, chainMoves: 0, dummyGaps: 0, permutationTrials: 0,
    jointSwapTrials: 0, jointSwapsAccepted: 0, jointSwapBudgetExhausted: 0 };
}
type Complete = { id: string; geometry: GraphGeometry; metrics: GeometryMetrics; proper: ProperGraph; placement: CorridorPlacement; ordering: Ordering };

/** A bounded beam, not a Cartesian product. Ranking, attachments, placement
 * and final routes are all candidate data; the renderer changes none of them.
 * This entry expects one acyclic component (SCCs use its condensation DAG). */
export function layoutDag(graph: MeasuredGraph, options: LayoutOptions): LayoutResult {
  const profile = options.profile ?? DEFAULT_PROFILE, stats = emptyStatistics(), diagnostics: Diagnostic[] = [];
  const select = <T extends { id: string; metrics: GeometryMetrics }>(candidates: readonly T[]): T =>
    options.optimizeCrossings ? [...candidates].sort(compareQuality)[0]! : selectCandidate(candidates);
  const phase = <T>(name: string, operation: () => T): T => {
    options.onPhase?.({ phase: name, start: true });
    try { return operation(); } finally { options.onPhase?.({ phase: name, start: false }); }
  };
  stats.components = graph.nodes.length ? 1 : 0;
  const ranking = phase("rank", () => rankGraph(graph, { pivotBudget: profile.rankPivots }));
  stats.rankPivots = ranking.pivots; stats.rankBudgetExhausted = ranking.termination === "budget-exhausted" ? 1 : 0;
  if (stats.rankBudgetExhausted) diagnostics.push({ code: "rank-budget-exhausted", message: "Feasible ranks retained without an optimality claim" });
  const rankVariants = [{ id: "simplex", ranks: ranking.ranks }];
  if (canonicalJson(ranking.ranks) !== canonicalJson(ranking.initialRanks)) rankVariants.push({ id: "longest-path", ranks: ranking.initialRanks });
  const structures: { id: string; proper: ProperGraph; ordering: Ordering }[] = [];
  for (const ranks of rankVariants) {
    const proper = phase("proper", () => makeProperGraph(graph, ranks.ranks, { expandedVertices: profile.expandedVertices, expandedSegments: profile.expandedVertices * 2, dummyWidth: profile.dummyGap }));
    stats.dummyVertices = Math.max(stats.dummyVertices, proper.dummyCount);
    stats.ranks = Math.max(stats.ranks, proper.layers.length);
    stats.maximumRankWidth = Math.max(stats.maximumRankWidth, ...proper.layers.map((layer) => layer.length), 0);
    const ordering = phase("order", () => orderGraph(proper, { sweeps: profile.sweeps, siftingMoves: profile.siftingMoves,
      dpStates: profile.dpStates, exactLayerLimit: profile.exactLayerLimit, candidates: 4, portSeparation: profile.portSeparation }));
    stats.sweeps += ordering.stats.sweeps; stats.siftingMoves += ordering.stats.siftingMoves; stats.dpStates += ordering.stats.dpStates;
    stats.chainMoves += ordering.stats.chainMoves;
    stats.permutationTrials += ordering.stats.permutationTrials;
    stats.jointSwapTrials += ordering.stats.jointSwapTrials;
    stats.jointSwapsAccepted += ordering.stats.jointSwapsAccepted;
    stats.jointSwapBudgetExhausted += ordering.stats.jointSwapBudgetExhausted;
    ordering.orderings.forEach((order, i) => structures.push({ id: `${ranks.id}:order-${i}`, proper, ordering: order }));
  }
  // Reserve representation of both rank assignments before crossing-score
  // pruning. A rank objective never selects the published drawing on its own.
  const beam = structures.filter((s) => s.id.endsWith("order-0"));
  for (const structure of [...structures].sort((a, b) => a.ordering.crossings - b.ordering.crossings || compareText(a.id, b.id)))
    if (beam.length < (options.optimizeCrossings ? 8 : 4) && !beam.includes(structure)) beam.push(structure);
  const complete: Complete[] = [], reports: CandidateReport[] = [], geometryKeys = new Set<string>();
  const remember = (id: string, geometry: GraphGeometry, proper: ProperGraph, placement: CorridorPlacement, ordering: Ordering): Complete | undefined => {
    const key = canonicalJson({ nodes: geometry.nodes, ports: geometry.ports, edges: geometry.edges });
    if (geometryKeys.has(key)) return undefined;
    geometryKeys.add(key); stats.candidates++;
    const checked = phase("validate", () => validateGeometry(graph, geometry));
    reports.push({ id, valid: checked.valid, metrics: checked.metrics, defects: [...new Set(checked.diagnostics.map((d) => d.code))] });
    if (!checked.valid) {
      diagnostics.push({ code: "candidate-rejected", message: `${id}: ${checked.diagnostics.slice(0, 6).map((d) => `${d.code} ${d.ids?.join("/") ?? ""}`).join(", ")}` });
      return undefined;
    }
    const candidate = { id, geometry, metrics: checked.metrics, proper, placement, ordering }; complete.push(candidate); return candidate;
  };
  const attempted: { id: string; proper: ProperGraph; placement: CorridorPlacement; geometry: GraphGeometry; ordering: Ordering }[] = [];
  for (const structure of beam) {
    const { proper, ordering } = structure;
    const coordinates: CoordinateCandidate[] = phase("coordinates-bk", () => [...coordinateCandidates(proper, ordering.layers, ordering.portOrder, profile)]);
    // The auxiliary candidate explicitly models fixed endpoint offsets. It is
    // independently feasible even if the coordinate pivot budget expires.
    const l1 = phase("coordinates-l1", () => coordinateL1(proper, ordering.layers, ordering.portOrder, profile));
    coordinates.push(l1); stats.coordinatePivots += l1.pivots;
    const balanced = coordinates.find((c) => c.id === "bk-balanced")!;
    coordinates.sort((a, b) => a.width - b.width || horizontalL1(proper, a.x, a.offsets) - horizontalL1(proper, b.x, b.offsets) || compareText(a.id, b.id));
    const chosen = options.optimizeCrossings ? coordinates : [balanced, coordinates[0]!];
    if (!options.optimizeCrossings && canonicalJson(chosen[0]!.x) === canonicalJson(chosen[1]!.x)) chosen.pop();
    for (const coordinate of chosen) {
      if (stats.candidates >= Math.max(1, profile.candidates - 3)) break;
      const id = `${structure.id}:${coordinate.id}:polyline`;
      const placement = phase("corridors", () => placeCorridors(proper, ordering.layers, coordinate.x, ordering.portOrder, profile, { offsets: coordinate.offsets }));
      const geometry = phase("route-protected", () => routeProtected(proper, placement, { inputDigest: options.inputDigest, profileId: profile.id }, profile));
      attempted.push({ id, proper, placement, geometry, ordering }); remember(id, geometry, proper, placement, ordering);
    }
  }
  // Orthogonal refinement has its own operation cap and competes on COMPLETE
  // geometry. If no polyline survives, it may still provide a safe candidate.
  const basis = complete.length ? select(complete) : attempted[0];
  const orthogonalCapacity = basis?.placement.bands.every((band) =>
    band.bottom - band.top >= (band.channels + 1) * profile.portSeparation);
  if (basis && orthogonalCapacity && graph.edges.length && stats.candidates < profile.candidates - 1) {
    const routed = phase("route-orthogonal-inclusive-validation", () => routeOrthogonalCandidates(basis.proper, basis.placement, basis.geometry, profile, { orders: Math.min(2, profile.candidates - stats.candidates - 1) }));
    stats.routingExpansions += routed.expansions; stats.visibilityVertices += routed.visibilityVertices; diagnostics.push(...routed.diagnostics);
    routed.candidates.forEach((geometry, i) => remember(`${basis.id}:orthogonal-${i}`, { ...geometry, profileId: profile.id }, basis.proper, basis.placement, basis.ordering));
  }
  if (!complete.length) throw new GraphDiagnosticError([{ code: "no-valid-layout", message: "Every complete candidate failed independent validation; no partial graph was emitted" }, ...diagnostics]);
  let selected = select(complete);
  if (options.optimizeCrossings && selected.metrics.crossings) {
    // Polish the actual routed drawing, not only the crossing estimate used
    // by layer ordering. Try adjacent node and free-port swaps, reroute each
    // complete candidate, and retain only independently validated reductions.
    const budget = Math.min(128, profile.siftingMoves);
    let trials = 0, improved = true;
    while (improved && selected.metrics.crossings && trials < budget) {
      improved = false;
      const current = selected;
      function* neighbours(): Generator<Ordering> {
        for (let rank = 0; rank < current.ordering.layers.length; rank++) {
          const row = current.ordering.layers[rank]!;
          for (let i = 1; i < row.length; i++) {
            const layers = current.ordering.layers.map((layer) => [...layer]);
            [layers[rank]![i - 1], layers[rank]![i]] = [row[i]!, row[i - 1]!];
            yield { ...current.ordering, layers };
          }
        }
        for (const node of graph.nodes) for (const side of ["north", "south", "east", "west"] as const) {
          const horizontal = side === "north" || side === "south";
          const ports = node.ports.filter((port) => port.side === side).sort((a, b) => {
            const p = current.placement.offsets[a.id]!, q = current.placement.offsets[b.id]!;
            return (horizontal ? p.x - q.x : p.y - q.y) || compareText(a.id, b.id);
          });
          for (let i = 1; i < ports.length; i++) {
            const free = (index: number) => ["free-on-side", "free-in-slots"].includes(ports[index]!.mode);
            if (!free(i - 1) || !free(i)) continue;
            const portOrder = { ...current.ordering.portOrder, ...Object.fromEntries(ports.map((port, j) => [port.id, j])) };
            portOrder[ports[i - 1]!.id] = i; portOrder[ports[i]!.id] = i - 1;
            yield { ...current.ordering, portOrder };
          }
        }
      }
      for (const ordering of neighbours()) {
        for (const coordinate of coordinateCandidates(current.proper, ordering.layers, ordering.portOrder, profile)) {
          if (trials++ >= budget) break;
          const placement = placeCorridors(current.proper, ordering.layers, coordinate.x, ordering.portOrder, profile, { offsets: coordinate.offsets });
          const geometry = routeProtected(current.proper, placement, { inputDigest: options.inputDigest, profileId: profile.id }, profile);
          const candidate = remember(`local-swap-${trials}`, geometry, current.proper, placement, ordering);
          if (candidate && candidate.metrics.crossings < selected.metrics.crossings) { selected = candidate; improved = true; }
        }
        if (improved || trials >= budget) break;
      }
    }
    if (trials >= budget && selected.metrics.crossings) diagnostics.push({ code: "local-crossing-budget-exhausted",
      message: "Local crossing search retained its best validated drawing after reaching the swap budget." });
  }
  if ((stats.candidates < profile.candidates || options.optimizeCrossings) && profile.cornerRadius > 0) {
    const refined = phase("round-inclusive-validation", () => validatedRounding(graph, selected.geometry, profile.cornerRadius));
    if (refined.rounded) {
      const candidate = remember(`${selected.id}:rounded`, refined.geometry, selected.proper, selected.placement, selected.ordering);
      // Rounding is cosmetic. The validator counts actual corners/arcs,
      // independently of the adaptive flattening used for collision tests.
      if (candidate && candidate.metrics.crossings <= selected.metrics.crossings) selected = candidate;
    }
  }
  const frontier = new Set(nondominated(complete).map((c) => c.id));
  stats.dummyGaps = dummyGaps(selected.proper, selected.proper.layers.map((row) => [...row].sort((a, b) => selected.placement.x[a]! - selected.placement.x[b]! || a - b)));
  return { geometry: selected.geometry, metrics: selected.metrics, diagnostics, stats,
    candidates: reports.map((r) => ({ ...r, selected: r.id === selected.id, nondominated: frontier.has(r.id) })),
    ...(options.retainCandidates ? { candidateGeometries: complete.filter((c) => frontier.has(c.id)).map(({ id, geometry, metrics }) => ({ id, geometry, metrics })) } : {}) };
}
