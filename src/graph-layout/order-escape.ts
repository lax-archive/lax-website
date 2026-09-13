import { attachmentPositions, countCrossings, countCrossingsAtRank, orderedPairCost, type AttachmentPositions } from "./cross-count.js";
import { constraintOrder, exactLayerOrder, type OrderConstraint } from "./order-exact.js";
import type { Ordering, PortOrder, ProperGraph } from "./proper-graph.js";

/** Enumerate a complete narrow layer only when its factorial fits the
 * caller's REMAINING move budget. Each anchored permutation proposes outward
 * barycenter orders, refreshes free attachments and polishes adjacent layers
 * with the existing fixed-neighbor DP. The combined search is a heuristic;
 * only each completed DP retains its fixed-neighbor optimality guarantee. */
export function escapeNarrowLayers(graph: ProperGraph, input: Ordering, options: {
  moveBudget: number; stateBudget: number; exactLayerLimit: number;
  portSeparation: number; constraints: readonly OrderConstraint[];
  proposePorts: (layers: readonly (readonly number[])[], ports: PortOrder) => PortOrder;
  remember: (ordering: Ordering) => void;
}): { ordering: Ordering; trials: number; states: number; transitions: number; portTrials: number; pairEvaluations: number } {
  let trials = 0, states = 0, transitions = 0, portTrials = 0, pairEvaluations = 0;
  const score = (layers: readonly (readonly number[])[], ports: PortOrder) => {
    const positions = attachmentPositions(graph, layers, ports, options.portSeparation);
    return { ordering: { layers, portOrder: ports, crossings: countCrossings(graph, layers, ports, options.portSeparation) }, positions,
      span: graph.segments.reduce((sum, _, i) => sum + Math.abs(positions.source[i]! - positions.target[i]!), 0) };
  };
  type Scored = ReturnType<typeof score>;
  const better = (a: Scored, b: Scored) => a.ordering.crossings < b.ordering.crossings ||
    a.ordering.crossings === b.ordering.crossings && a.span < b.span;
  let best = score(input.layers, input.portOrder);
  const offer = (candidate: Scored) => {
    options.remember(candidate.ordering);
    if (better(candidate, best)) best = candidate;
  };
  const refresh = (current: Scored): Scored => {
    portTrials++;
    const candidate = score(current.ordering.layers, options.proposePorts(current.ordering.layers, current.ordering.portOrder));
    offer(candidate);
    return better(candidate, current) ? candidate : current;
  };
  const constraints = graph.layers.map((_, rank) => options.constraints.filter(([u]) => graph.vertices[u]!.rank === rank));
  const lowerBound = (candidate: Scored, rank: number, start: number, length: number) => {
    // Ignore all within-node port constraints to obtain a LOWER bound that
    // remains valid even after free-port refresh. Outside a contiguous window
    // every node pair keeps its left/right relation. Inside it, independently
    // choosing the better orientation for each pair is an optimistic bound.
    const vertex = candidate.positions.vertex;
    const centers: AttachmentPositions = { vertex, source: graph.segments.map((segment) => vertex[segment.source]!),
      target: graph.segments.map((segment) => vertex[segment.target]!) };
    let value = graph.segmentsByRank.reduce((sum, _, boundary) => sum + countCrossingsAtRank(graph, boundary, centers), 0);
    const row = candidate.ordering.layers[rank]!.slice(start, start + length);
    for (let i = 0; i < row.length; i++) for (let j = i + 1; j < row.length; j++) {
      const forward = orderedPairCost(graph, centers, row[i]!, row[j]!), reverse = orderedPairCost(graph, centers, row[j]!, row[i]!);
      pairEvaluations += 2;
      value += Math.min(forward, reverse) - forward;
    }
    return value;
  };
  const factorialWithin = (length: number, budget: number) => {
    let count = 1;
    for (let i = 2; i <= length; i++) { count *= i; if (count > budget) return false; }
    return count <= budget;
  };
  const anchors = graph.layers.map((row, rank) => ({ rank, length: row.length }))
    .filter(({ length }) => length > 1 && length <= options.exactLayerLimit)
    .sort((a, b) => a.length - b.length || a.rank - b.rank);
  for (const { rank: anchor, length } of anchors) {
    if (best.ordering.crossings === 0) break;
    if (!factorialWithin(length, options.moveBudget - trials)) continue;
    const permutation = [...graph.layers[anchor]!].sort((a, b) => a - b);
    let more = true;
    while (more && trials < options.moveBudget && best.ordering.crossings > 0) {
      trials++;
      const legal = constraints[anchor]!.every(([u, v]) => permutation.indexOf(u) < permutation.indexOf(v));
      if (legal) {
        // Keep the best complete state as the starting point, preserving
        // unaffected layers and attachments across accepted escape proposals.
        const layers = best.ordering.layers.map((row) => [...row]);
        layers[anchor] = [...permutation];
        let candidate = refresh(score(layers, best.ordering.portOrder));
        // Refresh creates scored immutable candidates; never mutate the layer
        // arrays it gave to the portfolio while proposing another ordering.
        let trial = candidate.ordering.layers.map((row) => [...row]);
        for (const direction of [1, -1]) for (let rank = anchor + direction; rank >= 0 && rank < trial.length; rank += direction) {
          const positions = attachmentPositions(graph, trial, candidate.ordering.portOrder, options.portSeparation);
          const row = trial[rank]!, keys = new Map<number, number>();
          for (const v of row) {
            const incidences = direction > 0 ? graph.incoming[v]! : graph.outgoing[v]!;
            if (incidences.length) keys.set(v, incidences.reduce((sum, e) => sum + (direction > 0 ? positions.source[e]! : positions.target[e]!), 0) / incidences.length);
          }
          const movable = row.filter((v) => keys.has(v)).sort((a, b) => keys.get(a)! - keys.get(b)! || a - b);
          let next = 0;
          trial[rank] = constraintOrder(row, constraints[rank]!, row.map((v) => keys.has(v) ? movable[next++]! : v));
        }
        candidate = refresh(score(trial, candidate.ordering.portOrder));
        offer(candidate);
        for (const rank of [anchor - 1, anchor + 1]) {
          if (rank < 0 || rank >= trial.length) continue;
          const rowLength = candidate.ordering.layers[rank]!.length;
          const window = rowLength <= options.exactLayerLimit ? rowLength : Math.min(8, options.exactLayerLimit);
          if (window < 2) continue;
          for (let start = 0; start < rowLength && states < options.stateBudget; start += window) {
            const count = Math.min(window, rowLength - start);
            if (count < 2 || 2 ** count > options.stateBudget - states) continue;
            if (lowerBound(candidate, rank, start, count) > best.ordering.crossings) continue;
            const exact = exactLayerOrder(graph, candidate.ordering, rank, { constraints: constraints[rank],
              maxVertices: options.exactLayerLimit, stateBudget: options.stateBudget - states,
              start, length: count, portSeparation: options.portSeparation });
            states += exact.states; transitions += exact.transitions;
            if (exact.termination !== "optimal-for-fixed-neighbors") continue;
            trial = candidate.ordering.layers.map((row) => [...row]); trial[rank] = [...exact.order];
            const polished = refresh(score(trial, candidate.ordering.portOrder));
            offer(polished);
            if (better(polished, candidate)) candidate = polished;
          }
        }
      }
      // Lexicographic successor: bounded stack space, stable numeric order.
      let pivot = permutation.length - 2;
      while (pivot >= 0 && permutation[pivot]! >= permutation[pivot + 1]!) pivot--;
      if (pivot < 0) more = false;
      else {
        let successor = permutation.length - 1;
        while (permutation[successor]! <= permutation[pivot]!) successor--;
        [permutation[pivot], permutation[successor]] = [permutation[successor]!, permutation[pivot]!];
        for (let left = pivot + 1, right = permutation.length - 1; left < right; left++, right--)
          [permutation[left], permutation[right]] = [permutation[right]!, permutation[left]!];
      }
    }
  }
  return { ordering: best.ordering, trials, states, transitions, portTrials, pairEvaluations };
}
