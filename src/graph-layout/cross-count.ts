import { portOffsets } from "./ports.js";
import type { PortOrder, ProperGraph } from "./proper-graph.js";
import { GraphDiagnosticError } from "./types.js";

export type BoundaryEdge = Readonly<{ source: number; target: number; weight?: number }>;
export type AttachmentPositions = Readonly<{
  source: readonly number[]; target: readonly number[]; vertex: readonly number[];
}>;
export function checkedCrossingCount(value: number): number {
  if (!Number.isSafeInteger(value) || value < 0)
    throw new GraphDiagnosticError([{ code: "crossing-capacity", message: "Crossing count exceeds exact nonnegative integer arithmetic" }]);
  return value;
}

/** Barth–Mutzel–Jünger inversion reduction with a Fenwick accumulator.
 * Equal source positions are queried as a batch BEFORE insertion; equal
 * target positions use an inclusive prefix. A shared endpoint is therefore
 * never counted as an interior crossing. Different ports are not coalesced. */
export function countBoundaryCrossings(input: readonly BoundaryEdge[]): number {
  for (const edge of input) if (!Number.isFinite(edge.source) || !Number.isFinite(edge.target) || !Number.isSafeInteger(edge.weight ?? 1) || (edge.weight ?? 1) < 0)
    throw new GraphDiagnosticError([{ code: "crossing-input", message: "Boundary positions must be finite and multiplicities nonnegative safe integers" }]);
  const edges = [...input].sort((a, b) => a.source - b.source || a.target - b.target);
  const targets = [...new Set(edges.map((edge) => edge.target))].sort((a, b) => a - b);
  const index = new Map(targets.map((value, i) => [value, i + 1])), tree = new Float64Array(targets.length + 1);
  const prefix = (at: number) => { let count = 0; for (; at > 0; at -= at & -at) count += tree[at]!; return count; };
  let seen = 0, crossings = 0;
  for (let first = 0; first < edges.length;) {
    let last = first + 1; while (last < edges.length && edges[last]!.source === edges[first]!.source) last++;
    for (let at = first; at < last; at++) {
      const edge = edges[at]!, contribution = checkedCrossingCount((edge.weight ?? 1) * (seen - prefix(index.get(edge.target)!)));
      crossings = checkedCrossingCount(crossings + contribution);
    }
    for (let at = first; at < last; at++) {
      const edge = edges[at]!, weight = edge.weight ?? 1; seen = checkedCrossingCount(seen + weight);
      for (let pos = index.get(edge.target)!; pos < tree.length; pos += pos & -pos) tree[pos] = checkedCrossingCount(tree[pos]! + weight);
    }
    first = last;
  }
  return crossings;
}

/** Real boundary positions use the SAME finalized offsets as placement. The
 * arbitrary gap between integer vertex slots keeps distinct boxes disjoint;
 * only within-box order and equality matter to the bilayer objective. Side
 * adapters are evaluated again by the final geometry validator. */
export function attachmentPositions(graph: ProperGraph, layers: readonly (readonly number[])[], portOrder: PortOrder = {}, portSeparation = 8): AttachmentPositions {
  const vertex = new Array<number>(graph.vertices.length).fill(NaN), seen = new Uint8Array(graph.vertices.length);
  layers.forEach((layer, rank) => layer.forEach((v, position) => {
    if (!graph.vertices[v] || seen[v] || graph.vertices[v]!.rank !== rank)
      throw new GraphDiagnosticError([{ code: "layer-permutation", message: "Layers must contain each proper vertex exactly once at its assigned rank" }]);
    seen[v] = 1; vertex[v] = position * 2;
  }));
  if (seen.some((present) => !present)) throw new GraphDiagnosticError([{ code: "layer-permutation", message: "Layer ordering lost a proper vertex" }]);
  const offsets = portOffsets(graph.source, portOrder, portSeparation);
  const endpoint = (v: number, portId: string | undefined) => vertex[v]! + (portId ? offsets[portId]!.x / graph.vertices[v]!.width : 0.5);
  return { vertex, source: graph.segments.map((segment) => endpoint(segment.source, segment.sourcePortId)),
    target: graph.segments.map((segment) => endpoint(segment.target, segment.targetPortId)) };
}
export function countCrossingsAtRank(graph: ProperGraph, rank: number, positions: AttachmentPositions): number {
  return countBoundaryCrossings((graph.segmentsByRank[rank] ?? []).map((segment) => ({ source: positions.source[segment]!, target: positions.target[segment]! })));
}
export function countCrossings(graph: ProperGraph, layers: readonly (readonly number[])[], portOrder: PortOrder = {}, portSeparation = 8): number {
  const positions = attachmentPositions(graph, layers, portOrder, portSeparation);
  let count = 0;
  for (let rank = 0; rank < graph.segmentsByRank.length; rank++) count = checkedCrossingCount(count + countCrossingsAtRank(graph, rank, positions));
  return count;
}

/** c(u,v), with u before v. BOTH neighboring boundaries contribute. Terms
 * inside one node (including crossed fixed docks) are constant in this local
 * node permutation and are deliberately absent from this pair term. */
export function orderedPairCost(graph: ProperGraph, positions: AttachmentPositions, u: number, v: number): number {
  let count = 0;
  for (const a of graph.incoming[u]!) for (const b of graph.incoming[v]!) if (positions.source[a]! > positions.source[b]!) count++;
  for (const a of graph.outgoing[u]!) for (const b of graph.outgoing[v]!) if (positions.target[a]! > positions.target[b]!) count++;
  return checkedCrossingCount(count);
}
export function layerPairCosts(graph: ProperGraph, positions: AttachmentPositions, layer: readonly number[]): number[][] {
  return layer.map((u) => layer.map((v) => u === v ? 0 : orderedPairCost(graph, positions, u, v)));
}
