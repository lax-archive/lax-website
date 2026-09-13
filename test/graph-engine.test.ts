import { describe, expect, it } from "vitest";
import { layoutGraph, translateGeometry } from "../src/graph-layout/index.js";
import { canonicalJson } from "../src/graph-layout/normalize.js";
import { DEFAULT_PROFILE, type GraphGeometry, type MeasuredGraph, type MeasuredNode, type Point } from "../src/graph-layout/types.js";
import { validateGeometry } from "../src/graph-layout/validate.js";

/** Measured, distinctly attached fixture incidences. Their statement identity
 * remains fixed even when the input node, port and edge arrays are permuted. */
function fixture(count: number, pairs: readonly (readonly [number, number])[]): MeasuredGraph {
  const nodes: MeasuredNode[] = Array.from({ length: count }, (_, i) => {
    const width = 72 + i % 3 * 32, height = 32 + i % 2 * 16;
    const incoming = pairs.flatMap((pair, edge) => pair[1] === i ? [edge] : []);
    const outgoing = pairs.flatMap((pair, edge) => pair[0] === i ? [edge] : []);
    return { id: `n${i}`, kind: "concept", width, height,
      labelBoxes: [{ x: 8, y: 8, width: width - 16, height: 16 }],
      ports: [...incoming.map((edge, order) => ({ id: `e${edge}:target`, nodeId: `n${i}`,
        semanticEndpointId: `n${i}:statement:${edge}`, side: "south" as const, mode: "fixed-position" as const,
        offset: { x: width / 2 + (order - (incoming.length - 1) / 2) * 8, y: height } })),
      ...outgoing.map((edge, order) => ({ id: `e${edge}:source`, nodeId: `n${i}`,
        semanticEndpointId: `n${i}:statement:${edge}`, side: "north" as const, mode: "fixed-position" as const,
        offset: { x: width / 2 + (order - (outgoing.length - 1) / 2) * 8, y: 0 } }))] };
  });
  return { nodes, edges: pairs.map((_, edge) => ({ id: `e${edge}`, sourcePortId: `e${edge}:source`,
    targetPortId: `e${edge}:target`, kind: "dependency", minRankSpan: 1, semanticIds: [`semantic:${edge}`] })) };
}
const diamond = () => fixture(4, [[0, 1], [0, 2], [1, 3], [2, 3]]);
const skips = () => fixture(6, [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [0, 3], [0, 5], [2, 5]]);
const displayCycle = () => fixture(4, [[0, 1], [1, 2], [2, 1], [2, 3]]);
const draw = (graph: MeasuredGraph) => layoutGraph(graph, { inputDigest: "engine-fixture" });

function assertComplete(graph: MeasuredGraph, geometry: GraphGeometry): void {
  expect(validateGeometry(graph, geometry).diagnostics).toEqual([]);
  expect(geometry.nodes.map((node) => node.id).sort()).toEqual(graph.nodes.map((node) => node.id).sort());
  expect(geometry.ports.map((port) => port.id).sort()).toEqual(graph.nodes.flatMap((node) => node.ports.map((port) => port.id)).sort());
  expect(geometry.edges.map((edge) => edge.id).sort()).toEqual(graph.edges.map((edge) => edge.id).sort());
  for (const edge of graph.edges) {
    const terminal = geometry.edges.find((placed) => placed.id === edge.id)!.sections.filter((section) => section.terminalTargetPortId);
    expect(terminal).toHaveLength(1);
    expect(terminal[0]!.terminalTargetPortId).toBe(edge.targetPortId);
    const port = geometry.ports.find((placed) => placed.id === edge.targetPortId)!;
    expect(terminal[0]!.points.at(-1)).toEqual({ x: port.x, y: port.y });
  }
}

/** Independently remove only a component's packing translation, including
 * bends, rounded corners and SCC gates. This deliberately does not use the
 * production translateGeometry helper that packing itself calls. */
function relativeComponent(geometry: GraphGeometry, graph: MeasuredGraph) {
  const nodeIds = new Set(graph.nodes.map((node) => node.id));
  const edgeIds = new Set(graph.edges.map((edge) => edge.id));
  const origin = geometry.nodes.find((node) => node.id === graph.nodes[0]!.id)!;
  const point = (p: Point) => ({ x: Math.round((p.x - origin.x) * 1000) / 1000, y: Math.round((p.y - origin.y) * 1000) / 1000 });
  return {
    nodes: geometry.nodes.filter((node) => nodeIds.has(node.id)).map((node) => ({ ...node, ...point(node) })),
    ports: geometry.ports.filter((port) => nodeIds.has(port.nodeId)).map((port) => ({ ...port, ...point(port) })),
    edges: geometry.edges.filter((edge) => edgeIds.has(edge.id)).map((edge) => ({ ...edge, sections: edge.sections.map((section) => ({
      ...section, points: section.points.map(point), commands: section.commands?.map((command) => command.kind === "Q"
        ? { ...command, p: point(command.p), control: point(command.control) } : { ...command, p: point(command.p) }),
    })) })),
    groups: (geometry.groups ?? []).filter((group) => group.memberIds.every((id) => nodeIds.has(id))).map((group) => ({
      ...group, ...point(group), gates: group.gates?.map((gate) => ({ ...gate, point: point(gate.point) })),
    })),
  };
}

describe("the complete deterministic layout portfolio", () => {
  it("selects a straight path and a clear split/join for the diagnostic diamond", () => {
    const path = fixture(4, [[0, 1], [1, 2], [2, 3]]);
    const result = draw(path);
    assertComplete(path, result.geometry);
    expect(result.metrics).toMatchObject({ crossings: 0, bends: 0, overlaps: 0 });
    const splitJoin = draw(diamond());
    assertComplete(diamond(), splitJoin.geometry);
    expect(splitJoin.metrics).toMatchObject({ crossings: 0, overlaps: 0 });
  });

  it("retains all parallel incidences and all edges in an unavoidably crossing layer", () => {
    const dense = fixture(6, Array.from({ length: 3 }, (_, u) => Array.from({ length: 3 }, (_, v) => [u, v + 3] as const)).flat());
    const denseResult = draw(dense);
    assertComplete(dense, denseResult.geometry);
    expect(denseResult.metrics.crossings).toBeGreaterThan(0);
    expect(denseResult.metrics.overlaps).toBe(0);
    const parallel = fixture(2, [[0, 1], [0, 1], [0, 1]]), parallelResult = draw(parallel);
    assertComplete(parallel, parallelResult.geometry);
    expect(parallelResult.metrics.overlaps).toBe(0);
    expect(new Set(parallelResult.geometry.edges.map((edge) => canonicalJson(edge.sections[0]!.points))).size).toBe(3);
  });

  it("packs independent components in one horizontal row even beyond the preferred width", () => {
    const graph: MeasuredGraph = { nodes: Array.from({ length: 4 }, (_, i) => ({
      id: `wide-${i}`, kind: "concept", width: 700, height: 32, labelBoxes: [], ports: [],
    })), edges: [] };
    const result = draw(graph);
    assertComplete(graph, result.geometry);
    const nodes = [...result.geometry.nodes].sort((a, b) => a.x - b.x);
    expect(new Set(nodes.map((n) => n.y)).size).toBe(1);
    for (let i = 1; i < nodes.length; i++) expect(nodes[i]!.x).toBeGreaterThan(nodes[i - 1]!.x + nodes[i - 1]!.width);
  });

  it("reduces row gaps as a chain gains ranks without shrinking its nodes", () => {
    const gaps = [2, 4, 8, 16].map((count) => {
      const graph = fixture(count, Array.from({ length: count - 1 }, (_, i) => [i, i + 1] as const));
      const result = draw(graph);
      assertComplete(graph, result.geometry);
      const nodes = [...result.geometry.nodes].sort((a, b) => a.y - b.y);
      expect(nodes.map((n) => n.height).sort()).toEqual(graph.nodes.map((n) => n.height).sort());
      return nodes[1]!.y - nodes[0]!.y - nodes[0]!.height;
    });
    for (let i = 1; i < gaps.length; i++) expect(gaps[i]).toBeLessThan(gaps[i - 1]!);
    expect(Math.min(...gaps)).toBeGreaterThanOrEqual(32);
  });

  it.each([diamond, skips, displayCycle])("publishes identical bytes after independent input array permutations (%#)", (make) => {
    const graph = make(), first = draw(graph);
    for (let rotation = 0; rotation < 3; rotation++) {
      const reorder = <T>(items: readonly T[]) => [...items.slice(rotation), ...items.slice(0, rotation)].reverse();
      const shuffled = { nodes: reorder(graph.nodes).map((node) => ({ ...node, ports: reorder(node.ports) })), edges: reorder(graph.edges) };
      const other = draw(shuffled);
      assertComplete(shuffled, other.geometry);
      expect(canonicalJson(other.geometry)).toBe(canonicalJson(first.geometry));
      expect(other.stats).toEqual(first.stats);
      expect(other.candidates).toEqual(first.candidates);
    }
  });

  it.each([skips, displayCycle])("keeps every existing coordinate and route fixed up to packing translation after isolated additions (%#)", (make) => {
    const graph = make(), first = draw(graph);
    const enlarged: MeasuredGraph = { ...graph, nodes: [
      { id: "a-isolated", kind: "concept", width: 1100, height: 48, labelBoxes: [], ports: [] },
      ...graph.nodes,
      { id: "z-isolated", kind: "concept", width: 80, height: 32, labelBoxes: [], ports: [] },
    ] };
    const packed = draw(enlarged);
    assertComplete(enlarged, packed.geometry);
    expect(packed.stats.components).toBe(3);
    expect(relativeComponent(packed.geometry, graph)).toEqual(relativeComponent(first.geometry, graph));
  });

  it("preserves final geometric quality after translation across the coordinate origin", () => {
    const graph = skips(), original = draw(graph), shifted = translateGeometry(original.geometry, -173.25, -92.125);
    const validation = validateGeometry(graph, shifted);
    expect(validation.diagnostics).toEqual([]);
    for (const [metric, value] of Object.entries(original.metrics)) {
      if (typeof value === "number") expect(validation.metrics[metric as keyof typeof validation.metrics]).toBeCloseTo(value, 8);
      else expect(validation.metrics[metric as keyof typeof validation.metrics]).toBe(value);
    }
  });

  it("ignores dimension-preserving decoration and host instrumentation without mutating its input", () => {
    const graph = skips(), before = canonicalJson(graph), original = draw(graph);
    const decorated = { ...graph, nodes: graph.nodes.map((node) => ({ ...node,
      color: "#ff0000", status: "proven", privateView: "must-not-reach-geometry" })) };
    const phases: string[] = [];
    const other = layoutGraph(decorated, { inputDigest: "engine-fixture", onPhase: ({ phase, start }) => phases.push(`${phase}:${start}`) });
    expect(phases.length).toBeGreaterThan(0);
    expect(canonicalJson(other.geometry)).toBe(canonicalJson(original.geometry));
    expect(canonicalJson(graph)).toBe(before);
    expect(Object.isFrozen(graph.nodes[0]!.ports)).toBe(false);
    expect(Object.isFrozen(other.geometry.nodes[0])).toBe(true);
    expect(Object.isFrozen(other.geometry.edges[0]!.sections[0]!.points[0])).toBe(true);
    expect(canonicalJson(other.geometry)).not.toContain("must-not-reach-geometry");
  });

  it("retains complete feasible geometry under a small reproducible work budget", () => {
    const graph = skips();
    const profile = { ...DEFAULT_PROFILE, id: "bounded-fixture", rankPivots: 0, sweeps: 1,
      siftingMoves: 0, exactLayerLimit: 0, dpStates: 0, routingExpansions: 0, candidates: 3, cornerRadius: 0 };
    const result = layoutGraph(graph, { inputDigest: "bounded", profile });
    assertComplete(graph, result.geometry);
    expect(result.stats.rankPivots).toBe(0);
    expect(result.stats.dpStates).toBe(0);
    expect(result.stats.routingExpansions).toBe(0);
    expect(result.stats.candidates).toBeLessThanOrEqual(profile.candidates);
    expect(result.candidates.filter((candidate) => candidate.selected)).toHaveLength(1);
    expect(result.geometry.profileId).toBe(profile.id);
  });
});
