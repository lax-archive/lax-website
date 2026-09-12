import { describe, expect, it } from "vitest";
import { alignmentConflicts, assertSeparation, compactAligned, coordinateCandidates } from "../src/graph-layout/coordinates-bk.js";
import { portOffsets, placePorts } from "../src/graph-layout/ports.js";
import { makeProperGraph, type ProperGraph } from "../src/graph-layout/proper-graph.js";
import { DEFAULT_PROFILE, type MeasuredGraph, type MeasuredNode } from "../src/graph-layout/types.js";
import { coordinateL1 } from "../src/graph-layout/coordinates-l1.js";

const node = (id: string, width = 40): MeasuredNode => ({ id, kind: "concept", width, height: 24, labelBoxes: [], ports: [] });
function bareLayers(layers: number[][]): ProperGraph {
  const n = layers.flat().length, source = { nodes: Array.from({ length: n }, (_, i) => node(String(i), 10)), edges: [] };
  const graph = makeProperGraph(source, new Array(n).fill(0));
  return { ...graph, layers, vertices: graph.vertices.map((v) => ({ ...v, rank: layers.findIndex((layer) => layer.includes(v.index)) })) };
}
const compactProfile = { ...DEFAULT_PROFILE, nodeGap: 10 };
const erratum = () => {
  const graph = bareLayers([[0, 1], [2, 3, 4], [5, 6]]);
  return { graph, alignment: { root: [0, 1, 2, 3, 1, 5, 3], align: [0, 4, 2, 6, 1, 5, 3], potential: new Array(7).fill(0) } };
};

describe("corrected size-aware Brandes–Köpf coordinates", () => {
  it("erratum S: shifts each block member exactly once", () => {
    const { graph, alignment } = erratum(), output = compactAligned(graph, graph.layers, alignment, compactProfile);
    expect(output.shift[2]).toBe(-20);
    expect(output.x[3]).toBe(output.x[6]);
    expect(output.x[3]).toBe(0);
    // Copying the already shifted root and applying its shift again would
    // put member 6 at -20, separating an intended vertical block.
    expect(output.x[3]! + output.shift[2]!).not.toBe(output.x[6]);
  });
  it("erratum A: accumulates a nonzero shift through three classes", () => {
    const { graph, alignment } = erratum(), output = compactAligned(graph, graph.layers, alignment, compactProfile);
    expect(output.sink).toEqual([0, 0, 2, 2, 0, 5, 2]);
    expect(output.shift[5]).toBe(-20);
    expect(output.x[6]! - output.x[5]!).toBe(20);
    // Omitting the predecessor class shift places vertices 5 and 6 together.
    expect(output.relative[6]! - output.relative[5]! - 20).toBe(0);
  });
  it("rejects incompatible blocks instead of repairing node centers later", () => {
    const graph = bareLayers([[0, 1], [2, 3]]);
    expect(() => compactAligned(graph, graph.layers, { root: [0, 1, 1, 0], align: [3, 2, 1, 0], potential: [0, 0, 0, 0] })).toThrow(/alignment-cycle/);
  });
  it("marks BOTH crossing inner alignments unavailable", () => {
    const nodes = [node("a"), node("b"), node("c"), node("d")].map((n) => ({ ...n, ports: [
      { id: n.id + ":n", nodeId: n.id, semanticEndpointId: n.id, side: "north" as const, mode: "fixed-position" as const, offset: { x: 20, y: 0 } },
      { id: n.id + ":s", nodeId: n.id, semanticEndpointId: n.id, side: "south" as const, mode: "fixed-position" as const, offset: { x: 20, y: 24 } },
    ] }));
    const graph = makeProperGraph({ nodes, edges: [{ id: "ac", sourcePortId: "a:n", targetPortId: "c:s", kind: "import", minRankSpan: 1 }, { id: "bd", sourcePortId: "b:n", targetPortId: "d:s", kind: "import", minRankSpan: 1 }] }, [0, 0, 3, 3]);
    const layers = graph.layers.map((layer, rank) => rank === 2 ? [...layer].reverse() : [...layer]);
    const blocked = alignmentConflicts(graph, layers, portOffsets(graph.source));
    const inner = graph.segments.filter((edge) => graph.vertices[edge.source]!.nodeIndex === undefined && graph.vertices[edge.target]!.nodeIndex === undefined);
    expect(inner.every((edge) => blocked.has(edge.index))).toBe(true);
    for (const candidate of coordinateCandidates(graph, layers)) assertSeparation(graph, layers, candidate.x);
  });
  it("balances all four variants with unequal measured sizes", () => {
    const graph = bareLayers([[0, 1, 2], [3, 4], [5, 6]]);
    const sized = { ...graph, vertices: graph.vertices.map((v, i) => ({ ...v, width: [10, 190, 18, 85, 34, 12, 300][i]! })) };
    const candidates = coordinateCandidates(sized);
    expect(candidates.map((c) => c.id)).toEqual(["bk-up-left", "bk-up-right", "bk-down-left", "bk-down-right", "bk-balanced"]);
    for (const candidate of candidates) for (const layer of graph.layers) for (let i = 1; i < layer.length; i++) {
      const a = layer[i - 1]!, b = layer[i]!;
      expect(candidate.x[b]! - candidate.x[a]!).toBeGreaterThanOrEqual((sized.vertices[a]!.width + sized.vertices[b]!.width) / 2 + DEFAULT_PROFILE.nodeGap - 1e-6);
    }
  });
  it("aligns actual fixed attachment offsets, not box centers", () => {
    const source = { ...node("a", 80), ports: [{ id: "a:n", nodeId: "a", semanticEndpointId: "a:statement", side: "north" as const, mode: "fixed-position" as const, offset: { x: 64, y: 0 } }] };
    const target = { ...node("b", 120), ports: [{ id: "b:s", nodeId: "b", semanticEndpointId: "b:statement", side: "south" as const, mode: "fixed-position" as const, offset: { x: 16, y: 24 } }] };
    const graph = makeProperGraph({ nodes: [source, target], edges: [{ id: "e", sourcePortId: "a:n", targetPortId: "b:s", kind: "premise", minRankSpan: 1 }] }, [0, 1]);
    for (const candidate of coordinateCandidates(graph)) expect(candidate.x[0]! + 24).toBeCloseTo(candidate.x[1]! - 44);
  });
  it("supports empty and isolated graphs", () => {
    expect(coordinateCandidates(makeProperGraph({ nodes: [], edges: [] }, []))[4]!.x).toEqual([]);
    expect(coordinateCandidates(makeProperGraph({ nodes: [node("one")], edges: [] }, [0]))[4]!.x).toEqual([20]);
  });
});

describe("immutable semantic attachment placement", () => {
  it("preserves fixed dock identity and fixed order while preferring free order", () => {
    const graph: MeasuredGraph = { nodes: [{ ...node("n", 100), ports: [
      { id: "fixed", nodeId: "n", semanticEndpointId: "statement:2", side: "north", mode: "fixed-position", offset: { x: 88, y: 0 } },
      { id: "a", nodeId: "n", semanticEndpointId: "a", side: "north", mode: "fixed-order", order: 1 },
      { id: "b", nodeId: "n", semanticEndpointId: "b", side: "north", mode: "fixed-order", order: 2 },
      { id: "free", nodeId: "n", semanticEndpointId: "n", side: "north", mode: "free-on-side" },
    ] }], edges: [] };
    const offsets = portOffsets(graph, { b: 0, free: 1, a: 2 });
    expect(offsets.fixed).toEqual({ x: 88, y: 0 });
    expect(offsets.a!.x).toBeLessThan(offsets.b!.x);
    expect(offsets.free!.x).toBeLessThan(offsets.a!.x);
    const placed = placePorts(graph, [{ id: "n", x: 10, y: 30, width: 100, height: 24 }], offsets);
    expect(placed.find((p) => p.id === "fixed")).toMatchObject({ x: 98, y: 30 });
  });
  it("diagnoses a measured side without attachment capacity", () => {
    const n = node("n", 16), ports = [0, 1, 2].map((i) => ({ id: "p" + i, nodeId: "n", semanticEndpointId: "n", side: "north" as const, mode: "free-on-side" as const }));
    expect(() => portOffsets({ nodes: [{ ...n, ports }], edges: [] })).toThrow(/port-capacity/);
  });
});

describe("fixed-order auxiliary-graph L1 coordinates", () => {
  it("matches an independent integer enumeration oracle with fixed port offsets", () => {
    const pairs = [[0, 2], [0, 3], [1, 2], [1, 3]] as const;
    for (let variant = 0; variant < 5; variant++) {
      const nodes: MeasuredNode[] = Array.from({ length: 4 }, (_, i) => ({ id: String(i), kind: "concept", width: 2, height: 2, labelBoxes: [], ports: pairs.flatMap(([u, v], edge) => [
        ...(u === i ? [{ id: edge + ":s", nodeId: String(i), semanticEndpointId: String(i), side: "north" as const, mode: "fixed-position" as const, offset: { x: (edge + variant) % 3, y: 0 } }] : []),
        ...(v === i ? [{ id: edge + ":t", nodeId: String(i), semanticEndpointId: String(i), side: "south" as const, mode: "fixed-position" as const, offset: { x: (edge * 2 + variant) % 3, y: 2 } }] : []),
      ]) }));
      const graph = makeProperGraph({ nodes, edges: pairs.map((_, edge) => ({ id: String(edge), sourcePortId: edge + ":s", targetPortId: edge + ":t", kind: "import", minRankSpan: 1 })) }, [0, 0, 1, 1]);
      const result = coordinateL1(graph, graph.layers, {}, { ...DEFAULT_PROFILE, nodeGap: 0 });
      let optimum = Infinity;
      for (let a = 0; a <= 8; a++) for (let b = a + 2; b <= 8; b++) for (let c = 0; c <= 8; c++) for (let d = c + 2; d <= 8; d++) {
        const x = [a, b, c, d];
        const cost = pairs.reduce((sum, [u, v], edge) => sum + Math.abs(x[u]! + (edge + variant) % 3 - (x[v]! + (edge * 2 + variant) % 3)), 0);
        optimum = Math.min(optimum, cost);
      }
      expect(result.termination).toBe("optimal-for-rank-objective");
      expect(result.objective).toBeCloseTo(optimum);
      expect(result.objective).toBeLessThanOrEqual(result.initialObjective + 1e-6);
    }
  });
  it("keeps a feasible placement and honest termination after a zero pivot budget", () => {
    const graph = bareLayers([[0, 1, 2]]), result = coordinateL1(graph, graph.layers, {}, { ...DEFAULT_PROFILE, rankPivots: 0 });
    assertSeparation(graph, graph.layers, result.x);
    expect(result.pivots).toBe(0);
  });
});
