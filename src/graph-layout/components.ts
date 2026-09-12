import { GraphDiagnosticError, type MeasuredGraph } from "./types.js";

export type EndpointEdge = Readonly<{ source: number; target: number }>;
export type IndexedEdge = EndpointEdge & Readonly<{
  id: string; index: number; minRankSpan: number; weight: number;
}>;
export type IndexedGraph = Readonly<{ nodeCount: number; edges: readonly IndexedEdge[] }>;

/** The input has already passed normalizeGraph. These indexes keep ALL edge
 * incidences, including parallel edges and concept-level attachments. */
export function indexedGraph(graph: MeasuredGraph): IndexedGraph {
  const ports = new Map<string, number>();
  graph.nodes.forEach((node, index) => node.ports.forEach((port) => ports.set(port.id, index)));
  return { nodeCount: graph.nodes.length, edges: graph.edges.map((edge, index) => {
    const source = ports.get(edge.sourcePortId), target = ports.get(edge.targetPortId);
    if (source === undefined || target === undefined)
      throw new GraphDiagnosticError([{ code: "missing-endpoint", message: "An indexed edge has an absent semantic port", ids: [edge.id] }]);
    return { id: edge.id, index, source, target, minRankSpan: edge.minRankSpan, weight: edge.weight ?? 1 };
  }) };
}

/** Compact CSR adjacency; edge indexes recover multiplicity and identity. */
export function adjacency(nodeCount: number, edges: readonly EndpointEdge[], direction: "incoming" | "outgoing" | "undirected"): {
  offsets: Int32Array; neighbors: Int32Array; edgeIndexes: Int32Array;
} {
  if (!Number.isSafeInteger(nodeCount) || nodeCount < 0 || nodeCount >= 0x7fffffff || edges.length >= 0x3fffffff)
    throw new GraphDiagnosticError([{ code: "index-capacity", message: "Graph indexes exceed the supported CSR capacity" }]);
  const offsets = new Int32Array(nodeCount + 1);
  for (const edge of edges) {
    if (!Number.isInteger(edge.source) || !Number.isInteger(edge.target) || edge.source < 0 || edge.source >= nodeCount || edge.target < 0 || edge.target >= nodeCount)
      throw new GraphDiagnosticError([{ code: "missing-endpoint", message: "Graph edge has an invalid integer endpoint" }]);
    if (direction !== "incoming") offsets[edge.source + 1] = offsets[edge.source + 1]! + 1;
    if (direction !== "outgoing") offsets[edge.target + 1] = offsets[edge.target + 1]! + 1;
  }
  for (let i = 1; i < offsets.length; i++) offsets[i] = offsets[i]! + offsets[i - 1]!;
  const neighbors = new Int32Array(offsets[nodeCount]!), edgeIndexes = new Int32Array(neighbors.length), cursor = offsets.slice();
  edges.forEach((edge, index) => {
    const put = (u: number, v: number) => { const at = cursor[u]!; cursor[u] = at + 1; neighbors[at] = v; edgeIndexes[at] = index; };
    if (direction !== "incoming") put(edge.source, edge.target);
    if (direction !== "outgoing") put(edge.target, edge.source);
  });
  return { offsets, neighbors, edgeIndexes };
}

/** Components and their member indexes are in canonical integer order. */
export function weakComponents(nodeCount: number, edges: readonly EndpointEdge[]): number[][] {
  const { offsets, neighbors } = adjacency(nodeCount, edges, "undirected"), seen = new Uint8Array(nodeCount), result: number[][] = [];
  for (let start = 0; start < nodeCount; start++) {
    if (seen[start]) continue;
    const members = [start]; seen[start] = 1;
    for (let cursor = 0; cursor < members.length; cursor++) {
      const v = members[cursor]!;
      for (let at = offsets[v]!; at < offsets[v + 1]!; at++) {
        const w = neighbors[at]!;
        if (!seen[w]) { seen[w] = 1; members.push(w); }
      }
    }
    members.sort((a, b) => a - b); result.push(members);
  }
  return result;
}

/** Iterative Kosaraju: recursion depth is independent of path length. No edge
 * reversal escapes this traversal representation. */
export function stronglyConnectedComponents(nodeCount: number, edges: readonly EndpointEdge[]): number[][] {
  const forward = adjacency(nodeCount, edges, "outgoing"), reverse = adjacency(nodeCount, edges, "incoming");
  const seen = new Uint8Array(nodeCount), order: number[] = [];
  for (let start = 0; start < nodeCount; start++) {
    if (seen[start]) continue;
    const stack = [start], cursors = [forward.offsets[start]!]; seen[start] = 1;
    while (stack.length) {
      const top = stack.length - 1, v = stack[top]!, at = cursors[top]!;
      if (at === forward.offsets[v + 1]!) { stack.pop(); cursors.pop(); order.push(v); continue; }
      cursors[top] = at + 1;
      const w = forward.neighbors[at]!;
      if (!seen[w]) { seen[w] = 1; stack.push(w); cursors.push(forward.offsets[w]!); }
    }
  }
  seen.fill(0); const result: number[][] = [];
  for (let i = order.length - 1; i >= 0; i--) {
    const start = order[i]!;
    if (seen[start]) continue;
    const members = [start]; seen[start] = 1;
    for (let cursor = 0; cursor < members.length; cursor++) {
      const v = members[cursor]!;
      for (let at = reverse.offsets[v]!; at < reverse.offsets[v + 1]!; at++) {
        const w = reverse.neighbors[at]!;
        if (!seen[w]) { seen[w] = 1; members.push(w); }
      }
    }
    members.sort((a, b) => a - b); result.push(members);
  }
  return result.sort((a, b) => a[0]! - b[0]!);
}

/** Kahn's algorithm with a numeric min heap makes tie handling independent of
 * edge enumeration without the quadratic repeated sorting of ready queues. */
export function topologicalOrder(nodeCount: number, edges: readonly EndpointEdge[]): number[] {
  const { offsets, neighbors } = adjacency(nodeCount, edges, "outgoing"), degree = new Int32Array(nodeCount), heap: number[] = [], order: number[] = [];
  for (const edge of edges) degree[edge.target] = degree[edge.target]! + 1;
  const push = (value: number) => {
    let at = heap.length; heap.push(value);
    while (at) { const parent = (at - 1) >> 1; if (heap[parent]! <= value) break; heap[at] = heap[parent]!; at = parent; }
    heap[at] = value;
  };
  const pop = () => {
    const first = heap[0]!, last = heap.pop()!;
    if (heap.length) {
      let at = 0;
      while (at * 2 + 1 < heap.length) {
        let child = at * 2 + 1;
        if (child + 1 < heap.length && heap[child + 1]! < heap[child]!) child++;
        if (heap[child]! >= last) break;
        heap[at] = heap[child]!; at = child;
      }
      heap[at] = last;
    }
    return first;
  };
  for (let v = 0; v < nodeCount; v++) if (!degree[v]) push(v);
  while (heap.length) {
    const v = pop(); order.push(v);
    for (let at = offsets[v]!; at < offsets[v + 1]!; at++) {
      const w = neighbors[at]!; degree[w] = degree[w]! - 1; if (!degree[w]) push(w);
    }
  }
  if (order.length !== nodeCount) {
    const loops = new Set(edges.filter((e) => e.source === e.target).map((e) => e.source));
    const cyclic = stronglyConnectedComponents(nodeCount, edges).filter((c) => c.length > 1 || loops.has(c[0]!));
    throw new GraphDiagnosticError([{ code: "cyclic-rank-input", message: "Rank the display condensation DAG; internal SCC edges cannot satisfy positive DAG spans", ids: cyclic.flat().map(String) }]);
  }
  return order;
}

export function condensation(nodeCount: number, edges: readonly IndexedEdge[]): {
  components: number[][]; componentOf: number[]; edges: (IndexedEdge & { originalEdgeIndex: number })[]; internalEdges: number[][];
} {
  const components = stronglyConnectedComponents(nodeCount, edges), componentOf: number[] = new Array(nodeCount);
  components.forEach((members, component) => members.forEach((v) => { componentOf[v] = component; }));
  const outer: (IndexedEdge & { originalEdgeIndex: number })[] = [], internalEdges: number[][] = components.map(() => []);
  for (const edge of edges) {
    const source = componentOf[edge.source]!, target = componentOf[edge.target]!;
    if (source === target) internalEdges[source]!.push(edge.index);
    else outer.push({ ...edge, index: outer.length, source, target, originalEdgeIndex: edge.index });
  }
  return { components, componentOf, edges: outer, internalEdges };
}
