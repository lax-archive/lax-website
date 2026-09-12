/** Brandes–Köpf (2002), with BOTH Brandes–Walter–Zink (2020)
 * compaction corrections. See docs/graph-layout/placement-routing.md. */
import { centeredPortOffset, portOffsets, type PortOffsets } from "./ports.js";
import type { PortOrder, ProperGraph, ProperSegment } from "./proper-graph.js";
import { DEFAULT_PROFILE, GraphDiagnosticError, type LayoutProfile } from "./types.js";

export type CoordinateCandidate = Readonly<{
  id: string; x: readonly number[]; offsets: PortOffsets;
  rejectedAlignments: number; width: number;
}>;
export type Alignment = Readonly<{ root: readonly number[]; align: readonly number[]; potential: readonly number[] }>;
export type Compaction = Readonly<{ x: readonly number[]; relative: readonly number[]; sink: readonly number[]; shift: readonly number[] }>;
const fail = (code: string, message: string): never => { throw new GraphDiagnosticError([{ code, message }]); };

export function vertexSeparation(graph: ProperGraph, u: number, v: number, profile: LayoutProfile = DEFAULT_PROFILE): number {
  const a = graph.vertices[u]!, b = graph.vertices[v]!;
  return a.width / 2 + b.width / 2 + (a.nodeIndex === undefined || b.nodeIndex === undefined ? profile.dummyGap : profile.nodeGap);
}
export function segmentOffsets(graph: ProperGraph, segment: ProperSegment, offsets: PortOffsets): readonly [number, number] {
  const source = graph.vertices[segment.source]!, target = graph.vertices[segment.target]!;
  return [source.nodeIndex === undefined ? 0 : centeredPortOffset(graph.source.nodes[source.nodeIndex]!, segment.sourcePortId, offsets),
    target.nodeIndex === undefined ? 0 : centeredPortOffset(graph.source.nodes[target.nodeIndex]!, segment.targetPortId, offsets)];
}
function positions(layers: readonly (readonly number[])[], n: number): number[] {
  const pos = new Array<number>(n);
  for (const layer of layers) layer.forEach((v, p) => { pos[v] = p; });
  if (pos.some((p) => p === undefined) || layers.reduce((sum, layer) => sum + layer.length, 0) !== n || new Set(layers.flat()).size !== n)
    fail("coordinate-order", "Layers must contain every proper vertex exactly once");
  return pos;
}

/** Mark all type-1 conflicts and BOTH sides of a type-2 inner conflict.
 * Prefix/suffix extrema give O(m log m), without assuming dummy chains do
 * not cross. Attachment offsets distinguish different ports on one box. */
export function alignmentConflicts(graph: ProperGraph, layers: readonly (readonly number[])[], offsets: PortOffsets): Set<number> {
  const pos = positions(layers, graph.vertices.length), marked = new Set<number>();
  const endpoint = (v: number, offset: number) => pos[v]! + 0.5 + offset / Math.max(1, graph.vertices[v]!.width) * 0.98;
  for (const band of graph.segmentsByRank) {
    const data = band.map((i) => { const edge = graph.segments[i]!, [a, b] = segmentOffsets(graph, edge, offsets);
      return { i, a: endpoint(edge.source, a), b: endpoint(edge.target, b), inner: graph.vertices[edge.source]!.nodeIndex === undefined && graph.vertices[edge.target]!.nodeIndex === undefined }; });
    const inner = data.filter((e) => e.inner).sort((a, b) => a.a - b.a || a.b - b.b || a.i - b.i);
    if (!inner.length) continue;
    const prefix: number[] = [], suffix: number[] = [];
    for (let i = 0; i < inner.length; i++) prefix[i] = Math.max(i ? prefix[i - 1]! : -Infinity, inner[i]!.b);
    for (let i = inner.length - 1; i >= 0; i--) suffix[i] = Math.min(i + 1 < inner.length ? suffix[i + 1]! : Infinity, inner[i]!.b);
    for (const edge of data) {
      let low = 0, high = inner.length;
      while (low < high) { const middle = (low + high) >>> 1; if (inner[middle]!.a < edge.a) low = middle + 1; else high = middle; }
      const before = low;
      low = 0; high = inner.length;
      while (low < high) { const middle = (low + high) >>> 1; if (inner[middle]!.a <= edge.a) low = middle + 1; else high = middle; }
      if ((before > 0 && prefix[before - 1]! > edge.b) || (low < inner.length && suffix[low]! < edge.b)) marked.add(edge.i);
    }
  }
  return marked;
}

function verticalAlignment(graph: ProperGraph, layers: readonly (readonly number[])[], offsets: PortOffsets, blocked: Set<number>, descending: boolean, right: boolean): Alignment {
  const oriented = (descending ? [...layers].reverse() : [...layers]).map((layer) => right ? [...layer].reverse() : [...layer]);
  const n = graph.vertices.length, pos = positions(oriented, n), root = Array.from({ length: n }, (_, i) => i), align = [...root], potential = new Array<number>(n).fill(0);
  const sign = right ? -1 : 1;
  for (const layer of oriented) {
    let last = -1;
    for (const v of layer) {
      const incident = (descending ? graph.outgoing[v]! : graph.incoming[v]!).map((index) => {
        const segment = graph.segments[index]!, [source, target] = segmentOffsets(graph, segment, offsets);
        return { index, u: descending ? segment.target : segment.source, offsetU: sign * (descending ? target : source), offsetV: sign * (descending ? source : target) };
      }).sort((a, b) => pos[a.u]! - pos[b.u]! || a.offsetU - b.offsetU || a.index - b.index);
      const d = incident.length;
      if (!d) continue;
      for (const median of [Math.floor((d - 1) / 2), Math.floor(d / 2)]) {
        const edge = incident[median]!;
        if (align[v] === v && !blocked.has(edge.index) && last < pos[edge.u]!) {
          align[edge.u] = v; root[v] = root[edge.u]!; align[v] = root[v]!;
          potential[v] = potential[edge.u]! + edge.offsetU - edge.offsetV;
          last = pos[edge.u]!;
        }
      }
    }
  }
  return { root, align, potential };
}

/** Corrected compaction, expressed as explicit block and class DAG passes.
 * Coordinates are copied to ALL block members before any class shift, and
 * every shift is accumulated over the complete class DAG in dependency order.
 * This avoids both erroneous lines (S) and (A) in the original Algorithm 3. */
export function compactAligned(graph: ProperGraph, layers: readonly (readonly number[])[], alignment: Alignment, profile: LayoutProfile = DEFAULT_PROFILE): Compaction {
  const n = graph.vertices.length, { root, potential } = alignment, roots = [...new Set(root)];
  const layerOf = new Array<number>(n), pos = positions(layers, n);
  layers.forEach((layer, rank) => layer.forEach((v) => { layerOf[v] = rank; }));
  type Constraint = { u: number; v: number; gap: number };
  const incoming = Array.from({ length: n }, () => [] as Constraint[]), outgoing = Array.from({ length: n }, () => [] as Constraint[]), constraints: Constraint[] = [];
  const indegree = new Array<number>(n).fill(0);
  for (const layer of layers) for (let i = 1; i < layer.length; i++) {
    const a = layer[i - 1]!, b = layer[i]!, u = root[a]!, v = root[b]!;
    const gap = vertexSeparation(graph, a, b, profile) + potential[a]! - potential[b]!;
    if (u === v) fail("alignment-conflict", "An alignment block contains distinct vertices in one layer");
    const constraint = { u, v, gap }; incoming[v]!.push(constraint); outgoing[u]!.push(constraint); constraints.push(constraint); indegree[v]!++;
  }
  const queue = roots.filter((r) => indegree[r] === 0).sort((a, b) => layerOf[a]! - layerOf[b]! || pos[a]! - pos[b]! || a - b), order: number[] = [];
  for (let i = 0; i < queue.length; i++) { const u = queue[i]!; order.push(u); for (const edge of outgoing[u]!) if (!--indegree[edge.v]!) queue.push(edge.v); }
  if (order.length !== roots.length) fail("alignment-cycle", "Conflicting alignment blocks make cyclic separation constraints");
  const sink = new Array<number>(n), relativeRoot = new Array<number>(n).fill(0);
  const earlier = (a: number, b: number) => layerOf[a]! < layerOf[b]! || (layerOf[a] === layerOf[b] && (pos[a]! < pos[b]! || (pos[a] === pos[b] && a < b)));
  for (const v of order) {
    sink[v] = v;
    for (const edge of incoming[v]!) if (sink[v] === v || earlier(sink[edge.u]!, sink[v]!)) sink[v] = sink[edge.u]!;
    for (const edge of incoming[v]!) if (sink[edge.u] === sink[v]) relativeRoot[v] = Math.max(relativeRoot[v]!, relativeRoot[edge.u]! + edge.gap);
  }
  // Erratum (S): use immutable relativeRoot, not an already shifted root.
  const relative = root.map((r, v) => relativeRoot[r]! + potential[v]!);
  for (let v = 0; v < n; v++) sink[v] = sink[root[v]!]!;
  const classes = [...new Set(roots.map((r) => sink[r]!))], shift = new Array<number>(n).fill(Infinity);
  const classOut = Array.from({ length: n }, () => [] as { to: number; limit: number }[]), classDegree = new Array<number>(n).fill(0);
  for (const edge of constraints) if (sink[edge.u] !== sink[edge.v]) {
    // shift[left] <= shift[right] + rel[right] - rel[left] - separation.
    const from = sink[edge.v]!, to = sink[edge.u]!;
    classOut[from]!.push({ to, limit: relativeRoot[edge.v]! - relativeRoot[edge.u]! - edge.gap }); classDegree[to]!++;
  }
  const classQueue = classes.filter((c) => !classDegree[c]).sort((a, b) => layerOf[a]! - layerOf[b]! || a - b);
  for (const c of classQueue) shift[c] = 0;
  // Erratum (A): finish every predecessor's shift before using it downstream.
  for (let i = 0; i < classQueue.length; i++) for (const edge of classOut[classQueue[i]!]!) {
    shift[edge.to] = Math.min(shift[edge.to]!, shift[classQueue[i]!]! + edge.limit);
    if (!--classDegree[edge.to]!) classQueue.push(edge.to);
  }
  if (classQueue.length !== classes.length) fail("alignment-class-cycle", "Alignment classes contain cyclic shift constraints");
  const x = relative.map((value, v) => value + shift[sink[v]!]!);
  assertSeparation(graph, layers, x, profile);
  return { x, relative, sink, shift };
}

export function assertSeparation(graph: ProperGraph, layers: readonly (readonly number[])[], x: readonly number[], profile: LayoutProfile = DEFAULT_PROFILE): void {
  if (x.length !== graph.vertices.length || x.some((value) => !Number.isFinite(value))) fail("coordinate-nonfinite", "Coordinate candidate contains nonfinite or missing centers");
  for (const layer of layers) for (let i = 1; i < layer.length; i++) {
    const a = layer[i - 1]!, b = layer[i]!;
    if (x[b]! - x[a]! < vertexSeparation(graph, a, b, profile) - 1e-6) fail("coordinate-separation", `Order/clearance violation between ${graph.vertices[a]!.id} and ${graph.vertices[b]!.id}`);
  }
}
export function coordinateExtent(graph: ProperGraph, x: readonly number[]): readonly [number, number] {
  let low = Infinity, high = -Infinity;
  graph.vertices.forEach((vertex, i) => { low = Math.min(low, x[i]! - vertex.width / 2); high = Math.max(high, x[i]! + vertex.width / 2); });
  return graph.vertices.length ? [low, high] : [0, 0];
}
export function coordinateCandidates(graph: ProperGraph, layers: readonly (readonly number[])[] = graph.layers, order: PortOrder = {}, profile: LayoutProfile = DEFAULT_PROFILE): CoordinateCandidate[] {
  const offsets = portOffsets(graph.source, order, profile.portSeparation), blocked = alignmentConflicts(graph, layers, offsets);
  const candidates: CoordinateCandidate[] = [];
  for (const descending of [false, true]) for (const right of [false, true]) {
    const oriented = (descending ? [...layers].reverse() : [...layers]).map((layer) => right ? [...layer].reverse() : [...layer]);
    const alignment = verticalAlignment(graph, layers, offsets, blocked, descending, right);
    const compacted = compactAligned(graph, oriented, alignment, profile), x = compacted.x.map((value) => right ? -value : value);
    assertSeparation(graph, layers, x, profile);
    const [left, end] = coordinateExtent(graph, x);
    candidates.push({ id: `bk-${descending ? "down" : "up"}-${right ? "right" : "left"}`, x: x.map((value) => value - left), offsets, rejectedAlignments: blocked.size, width: end - left });
  }
  const narrowest = candidates.reduce((best, current) => current.width < best.width ? current : best);
  const aligned = candidates.map((candidate) => candidate.x.map((value) => value + (candidate.id.endsWith("right") ? narrowest.width - candidate.width : 0)));
  const x = graph.vertices.map((_, v) => { const values = aligned.map((candidate) => candidate[v]!).sort((a, b) => a - b); return (values[1]! + values[2]!) / 2; });
  assertSeparation(graph, layers, x, profile);
  const [left, end] = coordinateExtent(graph, x);
  candidates.push({ id: "bk-balanced", x: x.map((value) => value - left), offsets, rejectedAlignments: blocked.size, width: end - left });
  return candidates;
}
