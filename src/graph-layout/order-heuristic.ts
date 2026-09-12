import { attachmentPositions, checkedCrossingCount, countCrossings, orderedPairCost, type AttachmentPositions } from "./cross-count.js";
import { compareText } from "./normalize.js";
import { constraintOrder, exactLayerOrder, type OrderConstraint } from "./order-exact.js";
import { escapeNarrowLayers } from "./order-escape.js";
import type { Ordering, PortOrder, ProperGraph } from "./proper-graph.js";
import { GraphDiagnosticError } from "./types.js";
import { polishChains } from "./order-chain.js";

export type OrderOptions = Readonly<{
  sweeps?: number; siftingMoves?: number; exactLayerLimit?: number; dpStates?: number;
  candidates?: number; portSeparation?: number; constraints?: readonly OrderConstraint[];
  /** Comparison controls; production uses the fixed deterministic seed list. */
  seeds?: readonly number[];
}>;
export type OrderStats = { sweeps: number; siftingMoves: number; pairEvaluations: number;
  dpStates: number; dpTransitions: number; portTrials: number; seedCount: number; chainMoves: number; permutationTrials: number };
export type OrderSearch = Readonly<{ orderings: readonly Ordering[]; stats: Readonly<OrderStats> }>;
const copyLayers = (layers: readonly (readonly number[])[]) => layers.map((row) => [...row]);
const median = (values: readonly number[]) => { const sorted = [...values].sort((a, b) => a - b), mid = sorted.length >> 1; return sorted.length % 2 ? sorted[mid]! : (sorted[mid - 1]! + sorted[mid]!) / 2; };
const barycenter = (values: readonly number[]) => values.reduce((sum, value) => sum + value, 0) / values.length;
function orderKey(ordering: Ordering): string {
  return ordering.layers.map((row) => row.join(",")).join(";") + "|" + Object.keys(ordering.portOrder).sort(compareText).map((id) => JSON.stringify([id, ordering.portOrder[id]])).join(",");
}
function initialPortOrder(graph: ProperGraph): Record<string, number> {
  const result: Record<string, number> = Object.create(null);
  for (const node of graph.source.nodes) for (const side of ["north", "south", "east", "west"]) {
    const ports = node.ports.filter((port) => port.side === side && port.mode !== "fixed-position")
      .sort((a, b) => (a.order ?? Infinity) - (b.order ?? Infinity) || compareText(a.id, b.id));
    ports.forEach((port, index) => { result[port.id] = index; });
  }
  return result;
}

/** Reorder free-side incidences against opposite finalized attachments. Hard
 * fixed-order ports form an immutable subsequence; fixed positions are absent
 * from the permutation altogether. The WHOLE changed geometry topology is
 * rescored by the caller, never silently reordered in the renderer. */
export function proposePortOrder(graph: ProperGraph, layers: readonly (readonly number[])[], portOrder: PortOrder, portSeparation = 8): PortOrder {
  const positions = attachmentPositions(graph, layers, portOrder, portSeparation), opposite = new Map<string, number[]>();
  const append = (id: string | undefined, value: number) => { if (id) { const values = opposite.get(id) ?? []; values.push(value); opposite.set(id, values); } };
  graph.segments.forEach((segment, index) => { append(segment.sourcePortId, positions.target[index]!); append(segment.targetPortId, positions.source[index]!); });
  const result: Record<string, number> = { ...portOrder };
  for (const node of graph.source.nodes) for (const side of ["north", "south", "east", "west"]) {
    const ports = node.ports.filter((port) => port.side === side && port.mode !== "fixed-position");
    if (!ports.some((port) => port.mode === "free-on-side") || ports.length < 2) continue;
    const indexes = ports.map((_, i) => i), fixed = indexes.filter((i) => ports[i]!.mode === "fixed-order")
      .sort((a, b) => ports[a]!.order! - ports[b]!.order! || compareText(ports[a]!.id, ports[b]!.id));
    const constraints: OrderConstraint[] = fixed.slice(1).map((v, i) => [fixed[i]!, v]);
    const key = (i: number) => opposite.get(ports[i]!.id)?.length ? median(opposite.get(ports[i]!.id)!) : portOrder[ports[i]!.id] ?? i;
    const preference = [...indexes].sort((a, b) => key(a) - key(b) || (portOrder[ports[a]!.id] ?? a) - (portOrder[ports[b]!.id] ?? b) || compareText(ports[a]!.id, ports[b]!.id));
    constraintOrder(indexes, constraints, preference).forEach((port, ordinal) => { result[ports[port]!.id] = ordinal; });
  }
  return result;
}

function shuffled(layers: readonly (readonly number[])[], seed: number): number[][] {
  if (seed === 0) return copyLayers(layers);
  if (seed === -1) return layers.map((row) => [...row].reverse());
  let state = seed | 0;
  return layers.map((row) => {
    const result = [...row];
    for (let i = result.length - 1; i > 0; i--) {
      state = Math.imul(state, 1664525) + 1013904223 | 0;
      const j = (state >>> 0) % (i + 1); [result[i], result[j]] = [result[j]!, result[i]!];
    }
    return result;
  });
}

/** Bounded median/barycenter sweeps, adjacent swaps and whole-vertex sifting.
 * Call per weak component before packing. Exact polishing is an independent
 * local phase, not a global-optimum claim. Keeps the best COMPLETE states,
 * even when a sweep temporarily worsens a neighboring boundary. */
export function orderGraph(graph: ProperGraph, options: OrderOptions = {}): OrderSearch {
  const sweeps = options.sweeps ?? 8, moveBudget = options.siftingMoves ?? 4000, exactLimit = options.exactLayerLimit ?? 16;
  const dpBudget = options.dpStates ?? 2_000_000, keep = options.candidates ?? 4, separation = options.portSeparation ?? 8;
  for (const [name, value] of Object.entries({ sweeps, moveBudget, exactLimit, dpBudget, keep }))
    if (!Number.isSafeInteger(value) || value < 0 || name === "keep" && value < 1) throw new GraphDiagnosticError([{ code: "ordering-budget", message: `Invalid ${name} operation budget` }]);
  const constraintsByRank: OrderConstraint[][] = graph.layers.map(() => []);
  for (const constraint of options.constraints ?? []) {
    const u = graph.vertices[constraint[0]], v = graph.vertices[constraint[1]];
    if (!u || !v || u.rank !== v.rank) throw new GraphDiagnosticError([{ code: "order-constraint", message: "A hard order must join two existing vertices of one layer" }]);
    constraintsByRank[u.rank]!.push(constraint);
  }
  const seeds = options.seeds ?? [0, -1, 0x12345, 0x7654321];
  if (!seeds.length) throw new GraphDiagnosticError([{ code: "ordering-budget", message: "At least one deterministic ordering seed is required" }]);
  const stats: OrderStats = { sweeps: 0, siftingMoves: 0, pairEvaluations: 0, dpStates: 0, dpTransitions: 0, portTrials: 0, seedCount: 0, chainMoves: 0, permutationTrials: 0 };
  type Scored = { ordering: Ordering; span: number; key: string };
  const beam: Scored[] = [];
  const score = (layers: readonly (readonly number[])[], portOrder: PortOrder): Scored => {
    const positions = attachmentPositions(graph, layers, portOrder, separation);
    const ordering: Ordering = { layers, portOrder, crossings: countCrossings(graph, layers, portOrder, separation) };
    const span = graph.segments.reduce((sum, _, index) => sum + Math.abs(positions.source[index]! - positions.target[index]!), 0);
    return { ordering, span, key: orderKey(ordering) };
  };
  const compare = (a: Scored, b: Scored) => a.ordering.crossings - b.ordering.crossings || a.span - b.span || compareText(a.key, b.key);
  const remember = (candidate: Scored) => {
    if (beam.some((old) => old.key === candidate.key)) return;
    if (beam.length === keep && compare(candidate, beam.at(-1)!) >= 0) return;
    beam.push({ ...candidate, ordering: { ...candidate.ordering, layers: copyLayers(candidate.ordering.layers), portOrder: { ...candidate.ordering.portOrder } } });
    beam.sort(compare); if (beam.length > keep) beam.pop();
  };
  let escapeBudget = { moveBudget: 0, stateBudget: 0 };
  for (let seedIndex = 0; seedIndex < seeds.length; seedIndex++) {
    let layers = shuffled(graph.layers, seeds[seedIndex]!).map((row, rank) => constraintOrder(row, constraintsByRank[rank]!, row));
    let portOrder: PortOrder = initialPortOrder(graph), current = score(layers, portOrder), moves = 0, dpStates = 0;
    stats.seedCount++; remember(current);
    const center = seedIndex % 2 ? barycenter : median;
    const update = () => { current = score(layers, portOrder); remember(current); };
    const tryPorts = () => {
      const next = proposePortOrder(graph, layers, portOrder, separation), candidate = score(layers, next); stats.portTrials++;
      remember(candidate);
      if (compare(candidate, current) < 0) { portOrder = next; current = candidate; }
    };
    tryPorts();
    for (let pass = 0; pass < sweeps && graph.layers.some((row) => row.length > 1); pass++) {
      const ranks = layers.map((_, rank) => rank);
      const forward = (pass + seedIndex) % 2 === 0; if (!forward) ranks.reverse();
      for (const rank of ranks) {
        const row = layers[rank]!;
        if (row.length < 2) continue;
        const positions = attachmentPositions(graph, layers, portOrder, separation), keys = new Map<number, number>();
        for (const v of row) {
          const incidences = forward ? graph.incoming[v]! : graph.outgoing[v]!;
          if (incidences.length) keys.set(v, center(incidences.map((e) => forward ? positions.source[e]! : positions.target[e]!)));
        }
        const movable = row.filter((v) => keys.has(v)).sort((a, b) => keys.get(a)! - keys.get(b)! || positions.vertex[a]! - positions.vertex[b]! || a - b);
        let at = 0; const preference = row.map((v) => keys.has(v) ? movable[at++]! : v);
        layers[rank] = constraintOrder(row, constraintsByRank[rank]!, preference);
        update();
      }
      stats.sweeps++; tryPorts();
      // One bounded adjacent-swap pass. These incremental costs include both
      // neighboring boundaries, as do the later insertion/sifting trials.
      for (const rank of ranks) {
        const row = layers[rank]!;
        if (row.length < 2 || moves >= moveBudget) continue;
        const positions = attachmentPositions(graph, layers, portOrder, separation);
        for (let i = 0; i + 1 < row.length && moves < moveBudget; i++) {
          const u = row[i]!, v = row[i + 1]!; moves++; stats.siftingMoves++;
          if (constraintsByRank[rank]!.some(([a, b]) => a === u && b === v)) continue;
          stats.pairEvaluations += 2;
          if (orderedPairCost(graph, positions, v, u) < orderedPairCost(graph, positions, u, v)) [row[i], row[i + 1]] = [v, u];
        }
        update();
      }
    }
    // Degree-descending global vertex selection (and reverse on pass two)
    // follows the k-layer sifting method; each move scans every feasible
    // insertion slot using c(v,w)-c(w,v), retaining the best complete state.
    const siftOrder = graph.vertices.map((v) => v.index).sort((a, b) =>
      graph.incoming[b]!.length + graph.outgoing[b]!.length - graph.incoming[a]!.length - graph.outgoing[a]!.length || a - b);
    for (let pass = 0; pass < 2 && moves < moveBudget; pass++) {
      const vertices = pass ? [...siftOrder].reverse() : siftOrder;
      for (const v of vertices) {
        const rank = graph.vertices[v]!.rank, row = layers[rank]!;
        if (row.length < 2 || moves >= moveBudget) continue;
        const positions = attachmentPositions(graph, layers, portOrder, separation), others = row.filter((u) => u !== v), oldSlot = row.indexOf(v);
        const left = new Map<number, number>(), right = new Map<number, number>();
        for (const u of others) { left.set(u, orderedPairCost(graph, positions, v, u)); right.set(u, orderedPairCost(graph, positions, u, v)); stats.pairEvaluations += 2; }
        let cost = checkedCrossingCount(others.reduce((sum, u) => sum + left.get(u)!, 0)), bestSlot = oldSlot;
        const originalCost = others.reduce((sum, u, index) => sum + (index < oldSlot ? right.get(u)! : left.get(u)!), 0);
        let bestCost = originalCost;
        for (let slot = 0; slot <= others.length && moves < moveBudget; slot++) {
          moves++; stats.siftingMoves++;
          const legal = constraintsByRank[rank]!.every(([a, b]) => a === v ? slot <= others.indexOf(b) : b === v ? slot > others.indexOf(a) : true);
          if (legal && cost < bestCost) { bestCost = cost; bestSlot = slot; }
          if (slot < others.length) { const u = others[slot]!; cost = checkedCrossingCount(cost + right.get(u)! - left.get(u)!); }
        }
        if (bestSlot !== oldSlot) { others.splice(bestSlot, 0, v); layers[rank] = others; update(); }
      }
      tryPorts();
    }
    // Exact polishing uses canonical local indexes and shared DP-state budget
    // per seed. Wide layers get fixed contiguous windows, whose outside-node
    // pair costs are constant. No heuristic is relabeled as exact.
    for (let pass = 0; pass < 2 && exactLimit > 0 && dpStates < dpBudget; pass++) {
      const ranks = layers.map((_, rank) => rank); if (pass) ranks.reverse();
      for (const rank of ranks) {
        const length = layers[rank]!.length;
        if (length < 2) continue;
        const size = length <= exactLimit ? length : Math.min(exactLimit, 8);
        for (let start = 0; start < length && dpStates < dpBudget; start += size) {
          const window = Math.min(size, length - start); if (window < 2) continue;
          const polished = exactLayerOrder(graph, { layers, portOrder, crossings: current.ordering.crossings }, rank, {
            constraints: constraintsByRank[rank], maxVertices: exactLimit, stateBudget: dpBudget - dpStates, start, length: window, portSeparation: separation });
          dpStates += polished.states; stats.dpStates += polished.states; stats.dpTransitions += polished.transitions;
          if (polished.termination !== "optimal-for-fixed-neighbors") continue;
          const trial = copyLayers(layers); trial[rank] = [...polished.order];
          const candidate = score(trial, portOrder); remember(candidate);
          if (compare(candidate, current) < 0) { layers = trial; current = candidate; }
        }
      }
    }
    const remaining = { moveBudget: moveBudget - moves, stateBudget: dpBudget - dpStates };
    if (remaining.moveBudget > escapeBudget.moveBudget || remaining.moveBudget === escapeBudget.moveBudget && remaining.stateBudget > escapeBudget.stateBudget)
      escapeBudget = remaining;
    const chain = polishChains(graph, current.ordering, { moves: 32, portSeparation: separation, constraints: options.constraints });
    stats.chainMoves += chain.moves;
    remember(score(chain.ordering.layers, chain.ordering.portOrder));
    remember(current);
  }
  // Share the best state from every restart before a SINGLE narrow escape.
  // Spend only the unused budget of one restart; re-enumerating the same
  // anchored permutations after every seed adds duplicate work, not coverage.
  if (beam[0]!.ordering.crossings > 0 && escapeBudget.moveBudget > 0 && exactLimit > 0) {
    const escaped = escapeNarrowLayers(graph, beam[0]!.ordering, { ...escapeBudget,
      exactLayerLimit: exactLimit, portSeparation: separation, constraints: options.constraints ?? [],
      proposePorts: (trial, ports) => proposePortOrder(graph, trial, ports, separation),
      remember: (ordering) => remember(score(ordering.layers, ordering.portOrder)) });
    stats.permutationTrials += escaped.trials; stats.dpStates += escaped.states;
    stats.dpTransitions += escaped.transitions; stats.portTrials += escaped.portTrials; stats.pairEvaluations += escaped.pairEvaluations;
  }
  return { orderings: beam.map((candidate) => candidate.ordering), stats };
}
