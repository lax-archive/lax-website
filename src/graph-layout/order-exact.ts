import { attachmentPositions, checkedCrossingCount, layerPairCosts } from "./cross-count.js";
import type { Ordering, ProperGraph } from "./proper-graph.js";
import { GraphDiagnosticError } from "./types.js";

/** Each pair requires its first vertex/block before its second. */
export type OrderConstraint = readonly [number, number];
export type ExactOrderResult = Readonly<{
  order: readonly number[]; cost: number; states: number; transitions: number;
  termination: "optimal-for-fixed-neighbors" | "budget-exhausted" | "layer-too-wide";
}>;

export function constraintOrder(vertices: readonly number[], constraints: readonly OrderConstraint[], preference: readonly number[] = vertices): number[] {
  const members = new Set(vertices), pending = new Set(vertices), result: number[] = [];
  for (const [u, v] of constraints) if (!members.has(u) || !members.has(v))
    throw new GraphDiagnosticError([{ code: "order-constraint", message: "Ordering constraint names a vertex outside this layer" }]);
  while (pending.size) {
    const chosen = preference.find((v) => pending.has(v) && constraints.every(([before, after]) => after !== v || !pending.has(before)));
    if (chosen === undefined) throw new GraphDiagnosticError([{ code: "cyclic-order-constraint", message: "Hard ordering constraints have no valid permutation" }]);
    result.push(chosen); pending.delete(chosen);
  }
  return result;
}
export function permutationPairCost(costs: readonly (readonly number[])[], order: readonly number[]): number {
  let cost = 0;
  for (let i = 0; i < order.length; i++) for (let j = i + 1; j < order.length; j++) cost = checkedCrossingCount(cost + costs[order[i]!]![order[j]!]!);
  return cost;
}

/** Appending v charges every unordered pair exactly once, when its rightmost
 * member is appended. Direct O(k² 2^k) DP, O(2^k+k²) memory. No subset-sum
 * table is allocated. The optimum is LOCAL to these fixed neighbors/ports. */
export function subsetOrder(costs: readonly (readonly number[])[], constraints: readonly OrderConstraint[] = [], options: {
  maxVertices?: number; stateBudget?: number;
} = {}): ExactOrderResult {
  const k = costs.length, vertices = Array.from({ length: k }, (_, i) => i);
  if (costs.some((row) => row.length !== k || row.some((cost) => !Number.isSafeInteger(cost) || cost < 0)))
    throw new GraphDiagnosticError([{ code: "order-costs", message: "Exact ordering needs a square matrix of exact nonnegative pair costs" }]);
  const fallback = constraintOrder(vertices, constraints), base = { order: fallback, cost: permutationPairCost(costs, fallback), states: 0, transitions: 0 };
  const limit = Math.min(16, options.maxVertices ?? 16), budget = options.stateBudget ?? 2_000_000;
  if (!Number.isSafeInteger(limit) || limit < 0 || !Number.isSafeInteger(budget) || budget < 0)
    throw new GraphDiagnosticError([{ code: "order-budget", message: "Exact ordering budgets must be nonnegative integers" }]);
  if (k > limit) return { ...base, termination: "layer-too-wide" };
  const count = 2 ** k;
  if (count > budget) return { ...base, termination: "budget-exhausted" };
  const predecessors = new Int32Array(k);
  for (const [before, after] of constraints) predecessors[after] = predecessors[after]! | 1 << before;
  const dp = new Float64Array(count).fill(Infinity), appended = new Int8Array(count).fill(-1); dp[0] = 0;
  let states = 0, transitions = 0;
  for (let mask = 0; mask < count; mask++) {
    if (!Number.isFinite(dp[mask]!)) continue;
    states++;
    for (let v = 0; v < k; v++) {
      if (mask & 1 << v || (mask & predecessors[v]!) !== predecessors[v]) continue;
      let addition = 0;
      for (let u = 0; u < k; u++) if (mask & 1 << u) addition = checkedCrossingCount(addition + costs[u]![v]!);
      const next = mask | 1 << v, cost = checkedCrossingCount(dp[mask]! + addition); transitions++;
      // Fixed numeric mask/vertex iteration supplies deterministic equal-cost
      // ties. Callers canonicalize local vertex indexes before solving.
      if (cost < dp[next]!) { dp[next] = cost; appended[next] = v; }
    }
  }
  if (!Number.isFinite(dp[count - 1]!)) throw new GraphDiagnosticError([{ code: "cyclic-order-constraint", message: "No valid complete prefix in exact ordering" }]);
  const order: number[] = [];
  for (let mask = count - 1; mask;) { const v = appended[mask]!; order.push(v); mask ^= 1 << v; }
  order.reverse();
  return { order, cost: dp[count - 1]!, states, transitions, termination: "optimal-for-fixed-neighbors" };
}

/** An exact contiguous window can be embedded in a wider layer. Every vertex
 * outside the window stays on the same side of ALL moved vertices, so all
 * window/outside pair contributions are constant (and are included in final
 * whole-graph scoring). Noncontiguous windows are rejected. */
export function exactLayerOrder(graph: ProperGraph, ordering: Ordering, rank: number, options: {
  constraints?: readonly OrderConstraint[]; maxVertices?: number; stateBudget?: number;
  start?: number; length?: number; portSeparation?: number;
} = {}): ExactOrderResult {
  const layer = ordering.layers[rank];
  if (!layer) throw new GraphDiagnosticError([{ code: "order-rank", message: "Exact ordering names an absent rank" }]);
  const start = options.start ?? 0, length = options.length ?? layer.length;
  if (!Number.isInteger(start) || !Number.isInteger(length) || start < 0 || length < 0 || start + length > layer.length)
    throw new GraphDiagnosticError([{ code: "order-window", message: "Exact windows must be contiguous and inside one layer" }]);
  const fullConstraints = options.constraints ?? [];
  constraintOrder(layer, fullConstraints, layer);
  const canonical = layer.slice(start, start + length).sort((a, b) => a - b), index = new Map(canonical.map((v, i) => [v, i]));
  const positions = attachmentPositions(graph, ordering.layers, ordering.portOrder, options.portSeparation);
  const constraints: OrderConstraint[] = [];
  for (const [u, v] of fullConstraints) {
    if (index.has(u) && index.has(v)) constraints.push([index.get(u)!, index.get(v)!]);
    else if (layer.indexOf(u) > layer.indexOf(v)) throw new GraphDiagnosticError([{ code: "order-window-constraint", message: "A fixed outside-window order already violates a hard constraint" }]);
  }
  const result = subsetOrder(layerPairCosts(graph, positions, canonical), constraints, options);
  return { ...result, order: [...layer.slice(0, start), ...result.order.map((i) => canonical[i]!), ...layer.slice(start + length)] };
}
