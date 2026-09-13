import { describe, expect, it } from "vitest";
import { coordinateCandidates } from "../src/graph-layout/coordinates-bk.js";
import { placeCorridors, routeProtected } from "../src/graph-layout/corridors.js";
import { makeProperGraph } from "../src/graph-layout/proper-graph.js";
import { layoutGraph } from "../src/graph-layout/index.js";
import { pathData, polylineCommands } from "../src/graph-layout/geometry.js";
import { DEFAULT_PROFILE, type MeasuredGraph, type MeasuredNode } from "../src/graph-layout/types.js";
import { parsePathData, validateGeometry } from "../src/graph-layout/validate.js";
import { orthogonalPath, routeOrthogonalCandidates } from "../src/graph-layout/orthogonal-route.js";
import { terminalSafeCorners, validatedRounding } from "../src/graph-layout/route-refine.js";
import { measureDisplayGraph, projectGraph, type GraphLabel } from "../src/sitegen/graph-project.js";
import { graphSvg } from "../src/sitegen/graph-svg.js";

/** Frozen corpus 72dd74dd...122: its measured widths put both aligned ports
 * exactly halfway between published x coordinates. Different cancellation in
 * center - width/2 + width/2 formerly rounded them onto different grid lines. */
function halfQuantumFixture() {
  const display = projectGraph("concepts", { nodes: [
    { id: "Lax68.GraphMinors", title: "Graph minors", href: "../lax-68/Lax68.GraphMinors.html" },
    { id: "Lax68.GraphTopologicalMinors", title: "Topological graph minors", href: "../lax-68/Lax68.GraphTopologicalMinors.html" },
  ], edges: [{ from: "Lax68.GraphMinors", to: "Lax68.GraphTopologicalMinors" }] });
  const labels = new Map<string, GraphLabel>([
    ["Graph minors", { width: 72.90625, height: 16, lines: [{ text: "Graph minors", x: 0, y: 12, ink: { x: 0, y: 2, width: 72.90625, height: 12 } }] }],
    ["Topological graph minors", { width: 133.76095581054688, height: 16, lines: [{ text: "Topological graph minors", x: 0, y: 12, ink: { x: 0, y: 1.5, width: 133.76095581054688, height: 13 } }] }],
  ]);
  return measureDisplayGraph(display, labels);
}

export function routedFixture(count: number, pairs: readonly (readonly [number, number])[], ranks: readonly number[], widths?: number[]) {
  const nodes: MeasuredNode[] = Array.from({ length: count }, (_, i) => {
    const ins = pairs.filter((pair) => pair[1] === i).length, outs = pairs.filter((pair) => pair[0] === i).length;
    const width = Math.max(widths?.[i] ?? 60, 24 + Math.max(ins - 1, outs - 1) * 8);
    const incoming = pairs.map((pair, index) => ({ pair, index })).filter(({ pair }) => pair[1] === i), outgoing = pairs.map((pair, index) => ({ pair, index })).filter(({ pair }) => pair[0] === i);
    return { id: "n" + i, kind: "concept", width, height: 24 + i % 3 * 10, labelBoxes: [{ x: 8, y: 5, width: width - 16, height: 12 }], ports: [
      ...incoming.map(({ index }, ordinal) => ({ id: `e${index}:t`, nodeId: "n" + i, semanticEndpointId: "n" + i, side: "south" as const, mode: "fixed-position" as const, offset: { x: width / 2 + (ordinal - (incoming.length - 1) / 2) * 8, y: 24 + i % 3 * 10 } })),
      ...outgoing.map(({ index }, ordinal) => ({ id: `e${index}:s`, nodeId: "n" + i, semanticEndpointId: "n" + i, side: "north" as const, mode: "fixed-position" as const, offset: { x: width / 2 + (ordinal - (outgoing.length - 1) / 2) * 8, y: 0 } })),
    ] };
  });
  const source: MeasuredGraph = { nodes, edges: pairs.map((_, i) => ({ id: "e" + i, sourcePortId: `e${i}:s`, targetPortId: `e${i}:t`, kind: "import", minRankSpan: 1 })) };
  const graph = makeProperGraph(source, ranks);
  const coordinate = coordinateCandidates(graph).at(-1)!;
  const placement = placeCorridors(graph, graph.layers, coordinate.x, {}, DEFAULT_PROFILE, { offsets: coordinate.offsets });
  return { graph, placement, geometry: routeProtected(graph, placement) };
}

describe("protected proper-layer polyline geometry", () => {
  it("keeps fractional-width corpus terminals straight through quantization and SVG serialization", () => {
    const measured = halfQuantumFixture(), graph = makeProperGraph(measured.graph, [0, 1]);
    expect(measured.graph.nodes.map((node) => node.width)).toEqual([92.907, 153.761]);
    for (const coordinate of coordinateCandidates(graph)) {
      const placement = placeCorridors(graph, graph.layers, coordinate.x, {}, DEFAULT_PROFILE, { offsets: coordinate.offsets });
      const geometry = routeProtected(graph, placement);
      expect(validateGeometry(measured.graph, geometry)).toMatchObject({ valid: true, metrics: { bends: 0, crossings: 0 } });
      expect(geometry.ports[0]!.x).toBe(geometry.ports[1]!.x);
    }
    const geometry = layoutGraph(measured.graph, { inputDigest: "frozen-half-quantum" }).geometry;
    const svg = graphSvg(measured, geometry, "half-quantum");
    const route = /<path class="dag-edge"[^>]*\sd="([^"]+)"/u.exec(svg)![1]!;
    const commands = parsePathData(route);
    expect(commands).toHaveLength(2);
    expect(commands[0]!.p.x).toBe(commands[1]!.p.x);
    expect(svg).toContain('href="../lax-68/Lax68.GraphTopologicalMinors.html" role="link"');
    expect(svg).toContain('marker-end="url(#graph-arrow-half-quantum)"');
  });

  it("retains protected terminal stubs when a near-collinear candidate spans two quantized x positions", () => {
    const measured = halfQuantumFixture(), graph = makeProperGraph(measured.graph, [0, 1]);
    const coordinate = coordinateCandidates(graph).at(-1)!;
    // This displacement is larger than floating-point tie noise, yet small
    // enough to fool pre-quantization collinearity simplification. Distinct
    // published x positions must retain their two normal terminal approaches.
    const x = coordinate.x.map((value, i) => value - (i === 0 ? 1e-10 : 0));
    const placement = placeCorridors(graph, graph.layers, x, {}, DEFAULT_PROFILE, { offsets: coordinate.offsets });
    const geometry = routeProtected(graph, placement);
    const points = geometry.edges[0]!.sections[0]!.points;
    expect(points).toHaveLength(4);
    expect(points[0]!.x).toBe(points[1]!.x);
    expect(points[2]!.x).toBe(points[3]!.x);
    expect(points[0]!.x).not.toBe(points[3]!.x);
    const serialized = { ...geometry, edges: geometry.edges.map((edge) => ({ ...edge, sections: edge.sections.map((section) => ({
      ...section, commands: parsePathData(pathData(polylineCommands(section.points))),
    })) })) };
    expect(validateGeometry(measured.graph, serialized).diagnostics).toEqual([]);
    expect(() => graphSvg(measured, serialized, "near-half-quantum")).not.toThrow();
  });

  it("draws a path straight, with true upward edges and measured ports", () => {
    const { graph, geometry } = routedFixture(3, [[0, 1], [1, 2]], [0, 1, 2]);
    expect(validateGeometry(graph.source, geometry)).toMatchObject({ valid: true, metrics: { crossings: 0, overlaps: 0, bends: 0 } });
  });
  it("draws a clear diamond and retains every incidence", () => {
    const { graph, geometry } = routedFixture(4, [[0, 1], [0, 2], [1, 3], [2, 3]], [0, 1, 1, 2]);
    expect(validateGeometry(graph.source, geometry)).toMatchObject({ valid: true, metrics: { crossings: 0, overlaps: 0 } });
    expect(geometry.edges.map((e) => e.id)).toEqual(graph.source.edges.map((e) => e.id));
  });
  it("routes long skips through their slots outside every complete row", () => {
    const { graph, geometry } = routedFixture(6, [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [0, 5]], [0, 1, 2, 3, 4, 5], [80, 180, 40, 230, 40, 80]);
    const validation = validateGeometry(graph.source, geometry);
    expect(validation.diagnostics).toEqual([]);
    expect(validation.valid).toBe(true);
    expect(graph.dummyCount).toBe(4);
    expect(geometry.edges.at(-1)!.sections[0]!.points.length).toBeGreaterThan(2);
  });
  it("keeps dense unavoidable crossings without hidden edges or coincident stems", () => {
    const pairs = Array.from({ length: 4 }, (_, u) => Array.from({ length: 4 }, (_, v) => [u, 4 + v] as const)).flat();
    const { graph, geometry } = routedFixture(8, pairs, [0, 0, 0, 0, 1, 1, 1, 1]);
    const validation = validateGeometry(graph.source, geometry);
    expect(validation.diagnostics).toEqual([]);
    expect(validation.metrics.crossings).toBeGreaterThan(0);
    expect(geometry.edges).toHaveLength(16);
  });
  it("increases channel space for high incidence pressure", () => {
    const small = routedFixture(2, [[0, 1]], [0, 1]);
    const pairs = Array.from({ length: 20 }, (_, i) => [i, 20] as const);
    const large = routedFixture(21, pairs, [...new Array(20).fill(0), 1]);
    expect(large.placement.bands[0]!.bottom - large.placement.bands[0]!.top).toBeGreaterThan(small.placement.bands[0]!.bottom - small.placement.bands[0]!.top);
    expect(validateGeometry(large.graph.source, large.geometry).diagnostics).toEqual([]);
  });
  it("keeps native empty and single-node geometry complete", () => {
    for (const fixture of [routedFixture(0, [], []), routedFixture(1, [], [0])]) expect(validateGeometry(fixture.graph.source, fixture.geometry).valid).toBe(true);
  });
  it("independently validates every BK variant on deterministic varied-width DAGs", () => {
    let state = 7823;
    const random = () => { state = Math.imul(state, 1664525) + 1013904223 | 0; return (state >>> 0) / 2 ** 32; };
    for (let fixture = 0; fixture < 40; fixture++) {
      const ranks = Array.from({ length: 10 }, (_, i) => Math.floor(i / 2)), pairs: [number, number][] = [];
      for (let u = 0; u < 10; u++) for (let v = u + 1; v < 10; v++) if (ranks[v]! > ranks[u]! && random() < 0.16) pairs.push([u, v]);
      const { graph } = routedFixture(10, pairs, ranks, Array.from({ length: 10 }, () => 40 + Math.floor(random() * 160)));
      for (const coordinate of coordinateCandidates(graph)) {
        const placement = placeCorridors(graph, graph.layers, coordinate.x, {}, DEFAULT_PROFILE, { offsets: coordinate.offsets });
        const validation = validateGeometry(graph.source, routeProtected(graph, placement));
        expect(validation.diagnostics).toEqual([]);
      }
    }
  });
});

describe("direction-state object-avoiding orthogonal routing", () => {
  it("matches an independent unit-grid Bellman–Ford oracle", () => {
    const obstacle = { x: 2, y: 2, width: 2, height: 2 }, bendPenalty = 3;
    const result = orthogonalPath({ x: 0, y: 6 }, { x: 6, y: 0 }, { bounds: { x: 0, y: 0, width: 6, height: 6 }, obstacles: [obstacle], bendPenalty,
      startDirection: "north", targetDirection: "north", requireStartDirection: true, requireTargetDirection: true });
    // Independent oracle stores integer-grid (x,y,direction) distances and
    // relaxes ALL legal unit moves, without visibility graphs or a heap.
    const index = (x: number, y: number, d: number) => (y * 7 + x) * 4 + d;
    const distances = new Array(7 * 7 * 4).fill(Infinity); distances[index(0, 6, 0)] = 0;
    const delta = [[0, -1], [1, 0], [0, 1], [-1, 0]];
    for (let pass = 0; pass < distances.length; pass++) {
      let changed = false;
      for (let y = 0; y <= 6; y++) for (let x = 0; x <= 6; x++) for (let d = 0; d < 4; d++) for (const next of [0, 1, 3]) {
        if ((d + 2) % 4 === next || (x === 0 && y === 6 && d === 0 && next !== 0)) continue;
        const nx = x + delta[next]![0]!, ny = y + delta[next]![1]!;
        if (nx < 0 || nx > 6 || ny < 0 || ny > 6) continue;
        const mx = (x + nx) / 2, my = (y + ny) / 2;
        if (mx > 2 && mx < 4 && my > 2 && my < 4) continue;
        const cost = distances[index(x, y, d)]! + 1 + (d === next ? 0 : bendPenalty), at = index(nx, ny, next);
        if (cost < distances[at]!) { distances[at] = cost; changed = true; }
      }
      if (!changed) break;
    }
    expect(result.termination).toBe("shortest-in-visibility-graph");
    expect(result.cost).toBe(distances[index(6, 0, 0)]);
    expect(result.points![1]!.x).toBe(0);
    expect(result.points!.at(-2)!.x).toBe(6);
  });
  it("rejects coincident runs and reserves independent parallel lanes", () => {
    const result = orthogonalPath({ x: 0, y: 10 }, { x: 0, y: 0 }, { bounds: { x: -5, y: 0, width: 10, height: 10 },
      interesting: [{ x: 4, y: 2 }, { x: 4, y: 8 }], fixedRoutes: [[{ x: 0, y: 8 }, { x: 0, y: 2 }]] });
    expect(result.points).toBeDefined();
    expect(result.points!.some((p) => p.x === 4)).toBe(true);
  });
  it("reports exhaustion instead of returning a partial connector", () => {
    const result = orthogonalPath({ x: 0, y: 10 }, { x: 10, y: 0 }, { bounds: { x: 0, y: 0, width: 10, height: 10 }, expansionBudget: 0 });
    expect(result.termination).toBe("budget-exhausted");
    expect(result.points).toBeUndefined();
  });
  it("validates complete orthogonal diamond and dense candidates", () => {
    for (const { graph, placement, geometry } of [routedFixture(4, [[0, 1], [0, 2], [1, 3], [2, 3]], [0, 1, 1, 2]),
      routedFixture(4, [[0, 2], [0, 3], [1, 2], [1, 3]], [0, 0, 1, 1])]) {
      const result = routeOrthogonalCandidates(graph, placement, geometry);
      expect(result.candidates.length).toBeGreaterThan(0);
      for (const candidate of result.candidates) {
        expect(validateGeometry(graph.source, candidate).diagnostics).toEqual([]);
        for (const edge of candidate.edges) for (const section of edge.sections) for (let i = 1; i < section.points.length; i++)
          expect(section.points[i]!.x === section.points[i - 1]!.x || section.points[i]!.y === section.points[i - 1]!.y).toBe(true);
      }
    }
  });
  it("preserves terminal normals after quantized corner generation", () => {
    const points = [{ x: 0, y: 40 }, { x: 0, y: 28 }, { x: 20, y: 12 }, { x: 20, y: 0 }];
    const commands = terminalSafeCorners(points, 4);
    expect(commands[1]!.p.y).toBeLessThanOrEqual(30);
    expect(commands.at(-2)!.p.y).toBeGreaterThanOrEqual(10);
    const { graph, geometry } = routedFixture(4, [[0, 1], [0, 2], [1, 3], [2, 3]], [0, 1, 1, 2]);
    const result = validatedRounding(graph.source, geometry);
    expect(result.validation.valid).toBe(true);
    expect(result.validation.metrics.crossings).toBe(0);
  });
});
