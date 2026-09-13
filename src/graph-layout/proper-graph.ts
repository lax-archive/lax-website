import { indexedGraph } from "./components.js";
import { GraphDiagnosticError, type MeasuredGraph } from "./types.js";

/** Private optimization objects, never mathematical nodes in the SVG. */
export type ProperVertex = Readonly<{
  id: string; index: number; rank: number; width: number; height: number;
  nodeIndex?: number; edgeIndex?: number; chainOffset?: number;
}>;
export type ProperSegment = Readonly<{
  index: number; edgeIndex: number; source: number; target: number;
  sourcePortId?: string; targetPortId?: string;
}>;
/** Every list uses canonical integer indexes. Real nodes occupy the first
 * source.nodes.length positions; chains include both real endpoints. */
export type ProperGraph = Readonly<{
  source: MeasuredGraph;
  vertices: readonly ProperVertex[]; segments: readonly ProperSegment[];
  layers: readonly (readonly number[])[];
  incoming: readonly (readonly number[])[]; outgoing: readonly (readonly number[])[];
  segmentsByRank: readonly (readonly number[])[];
  chains: readonly (readonly number[])[]; dummyCount: number;
}>;
export type PortOrder = Readonly<Record<string, number>>;
export type Ordering = Readonly<{
  layers: readonly (readonly number[])[]; portOrder: PortOrder; crossings: number;
}>;

/** Explicit proper layering. Counts D before allocating any expanded arrays.
 * A budget failure is a diagnostic, never a partial graph. */
export function makeProperGraph(source: MeasuredGraph, ranks: readonly number[], options: {
  expandedVertices?: number; expandedSegments?: number; dummyWidth?: number;
} = {}): ProperGraph {
  const indexed = indexedGraph(source), n = source.nodes.length;
  const maxVertices = options.expandedVertices ?? 500_000;
  const maxSegments = options.expandedSegments ?? maxVertices + source.edges.length;
  const dummyWidth = options.dummyWidth ?? 8;
  const fail = (code: string, message: string): never => { throw new GraphDiagnosticError([{ code, message }]); };
  if (!Number.isSafeInteger(maxVertices) || maxVertices < 0 || !Number.isSafeInteger(maxSegments) || maxSegments < 0)
    fail("expansion-budget", "Expansion budgets must be nonnegative safe integers");
  if (ranks.length !== n || ranks.some((rank) => !Number.isSafeInteger(rank) || rank < 0))
    fail("proper-ranks", "Proper layering requires one nonnegative integer rank per node");
  if (!Number.isFinite(dummyWidth) || dummyWidth <= 0) fail("dummy-clearance", "Dummy width must reserve positive clearance");
  let dummyCount = 0, maximumRank = 0;
  for (const rank of ranks) maximumRank = Math.max(maximumRank, rank);
  for (const edge of indexed.edges) {
    const span = ranks[edge.target]! - ranks[edge.source]!;
    if (span < edge.minRankSpan) fail("proper-ranks", `Infeasible minimum span on ${edge.id}`);
    dummyCount += span - 1;
    if (!Number.isSafeInteger(dummyCount)) fail("expansion-overflow", "Dummy count exceeds exact integer arithmetic");
  }
  if (n + dummyCount > maxVertices || source.edges.length + dummyCount > maxSegments || (n && maximumRank + 1 > maxVertices))
    fail("expansion-budget", `Explicit layering needs ${n + dummyCount} vertices, ${source.edges.length + dummyCount} segments, and ${n ? maximumRank + 1 : 0} ranks; use a larger measured profile or a separately verified sparse backend`);
  const vertices: ProperVertex[] = source.nodes.map((node, index) => ({ id: node.id, index, rank: ranks[index]!, width: node.width, height: node.height, nodeIndex: index }));
  const segments: ProperSegment[] = [], chains: number[][] = [];
  const occupiedIds = new Set(source.nodes.map((node) => node.id));
  const layers: number[][] = Array.from({ length: n ? maximumRank + 1 : 0 }, () => []);
  const incoming: number[][] = Array.from({ length: n + dummyCount }, () => []);
  const outgoing: number[][] = Array.from({ length: n + dummyCount }, () => []);
  const segmentsByRank: number[][] = Array.from({ length: Math.max(0, layers.length - 1) }, () => []);
  for (const edge of indexed.edges) {
    const chain = [edge.source];
    for (let rank = ranks[edge.source]! + 1; rank < ranks[edge.target]!; rank++) {
      const index = vertices.length, chainOffset = rank - ranks[edge.source]!;
      let id = `layout:dummy:${JSON.stringify([edge.id, chainOffset])}`;
      while (occupiedIds.has(id)) id = ":" + id;
      occupiedIds.add(id);
      vertices.push({ id, index, rank, width: dummyWidth, height: 0, edgeIndex: edge.index, chainOffset });
      chain.push(index);
    }
    chain.push(edge.target); chains.push(chain);
    for (let offset = 0; offset + 1 < chain.length; offset++) {
      const index = segments.length, u = chain[offset]!, v = chain[offset + 1]!;
      segments.push({ index, edgeIndex: edge.index, source: u, target: v,
        ...(offset === 0 ? { sourcePortId: source.edges[edge.index]!.sourcePortId } : {}),
        ...(offset + 2 === chain.length ? { targetPortId: source.edges[edge.index]!.targetPortId } : {}) });
      outgoing[u]!.push(index); incoming[v]!.push(index); segmentsByRank[vertices[u]!.rank]!.push(index);
    }
  }
  for (const vertex of vertices) layers[vertex.rank]!.push(vertex.index);
  return { source, vertices, segments, layers, incoming, outgoing, segmentsByRank, chains, dummyCount };
}
