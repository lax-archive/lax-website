/** Gansner et al. auxiliary-graph coordinate objective, with explicit measured
 * endpoint offsets. This optimizes fixed-order horizontal L1 displacement;
 * it does not assert minimum drawing length or minimum routed crossings. */
import { assertSeparation, coordinateExtent, segmentOffsets, vertexSeparation, type CoordinateCandidate } from "./coordinates-bk.js";
import { portOffsets, type PortOffsets } from "./ports.js";
import type { PortOrder, ProperGraph } from "./proper-graph.js";
import { rankIndexed, type RankEdge } from "./rank-simplex.js";
import { DEFAULT_PROFILE, QUANTUM, type LayoutProfile } from "./types.js";

export type L1Candidate = CoordinateCandidate & Readonly<{
  objective: number; initialObjective: number; pivots: number;
  termination: "optimal-for-rank-objective" | "budget-exhausted";
}>;

export function horizontalL1(graph: ProperGraph, x: readonly number[], offsets: PortOffsets): number {
  return graph.segments.reduce((sum, segment) => {
    const [source, target] = segmentOffsets(graph, segment, offsets);
    return sum + Math.abs(x[segment.source]! + source - x[segment.target]! - target);
  }, 0);
}

export function coordinateL1(graph: ProperGraph, layers: readonly (readonly number[])[] = graph.layers, order: PortOrder = {}, profile: LayoutProfile = DEFAULT_PROFILE): L1Candidate {
  const offsets = portOffsets(graph.source, order, profile.portSeparation), edges: RankEdge[] = [], n = graph.vertices.length;
  const grid = (value: number) => Math.round(value / QUANTUM);
  for (const layer of layers) for (let i = 1; i < layer.length; i++) {
    const source = layer[i - 1]!, target = layer[i]!;
    // Round separation upward; coordinate quantization cannot violate it.
    edges.push({ id: `separation:${source}:${target}`, source, target,
      minRankSpan: Math.ceil(vertexSeparation(graph, source, target, profile) / QUANTUM), weight: 0 });
  }
  graph.segments.forEach((segment, i) => {
    const [source, target] = segmentOffsets(graph, segment, offsets), auxiliary = n + i;
    // a <= x(u)+source and a <= x(v)+target. Maximizing a minimizes
    // x(u)+source-a + x(v)+target-a = |endpoint(u)-endpoint(v)|.
    edges.push({ id: `l1:${i}:s`, source: auxiliary, target: segment.source, minRankSpan: -grid(source), weight: 1 },
      { id: `l1:${i}:t`, source: auxiliary, target: segment.target, minRankSpan: -grid(target), weight: 1 });
  });
  const result = rankIndexed(n + graph.segments.length, edges, { pivotBudget: profile.rankPivots });
  const centers = result.ranks.slice(0, n).map((rank) => rank * QUANTUM);
  const [left, right] = coordinateExtent(graph, centers), x = centers.map((value) => value - left);
  assertSeparation(graph, layers, x, profile);
  return { id: "l1-auxiliary", x, offsets, rejectedAlignments: 0, width: right - left,
    objective: horizontalL1(graph, x, offsets), initialObjective: horizontalL1(graph, result.initialRanks.slice(0, n).map((rank) => rank * QUANTUM), offsets),
    pivots: result.pivots, termination: result.termination };
}
