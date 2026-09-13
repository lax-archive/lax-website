import { describe, expect, it } from "vitest";
import { attachmentPositions, countBoundaryCrossings, countCrossings, layerPairCosts, orderedPairCost, type BoundaryEdge } from "../src/graph-layout/cross-count.js";
import { normalizeGraph } from "../src/graph-layout/normalize.js";
import { exactLayerOrder, subsetOrder, type OrderConstraint } from "../src/graph-layout/order-exact.js";
import { orderGraph, proposePortOrder } from "../src/graph-layout/order-heuristic.js";
import { polishJointSwaps } from "../src/graph-layout/order-joint.js";
import { portOffsets } from "../src/graph-layout/ports.js";
import { makeProperGraph, type Ordering, type ProperGraph } from "../src/graph-layout/proper-graph.js";
import { rankGraph } from "../src/graph-layout/rank-simplex.js";
import type { MeasuredGraph, MeasuredNode, PortSpec } from "../src/graph-layout/types.js";

type Pair = readonly [number, number];
function fixture(ranks: readonly number[], pairs: readonly Pair[], mode: PortSpec["mode"] = "fixed-position"): ProperGraph {
  const ids = ranks.map((_, i) => "n" + String(i).padStart(3, "0"));
  const nodes: MeasuredNode[] = ids.map((id, index) => {
    const input = pairs.map(([s, t], edge) => ({ s, t, edge })).filter((edge) => edge.t === index);
    const output = pairs.map(([s, t], edge) => ({ s, t, edge })).filter((edge) => edge.s === index);
    const width = 32 + 8 * Math.max(input.length, output.length, 1);
    const ports: PortSpec[] = [...output.map(({ edge }, at): PortSpec => ({ id: `s${edge}`, nodeId: id, semanticEndpointId: `statement:${index}:${edge}`,
      side: "north", mode, ...(mode === "fixed-position" ? { offset: { x: 16 + at * 8, y: 0 } } : mode === "fixed-order" ? { order: at } : {}) })),
    ...input.map(({ edge }, at): PortSpec => ({ id: `t${edge}`, nodeId: id, semanticEndpointId: `statement:${index}:${edge}`,
      side: "south", mode, ...(mode === "fixed-position" ? { offset: { x: 16 + at * 8, y: 24 } } : mode === "fixed-order" ? { order: at } : {}) }))];
    return { id, width, height: 24, kind: "concept", labelBoxes: [], ports };
  });
  const source = normalizeGraph({ nodes, edges: pairs.map((_, i) => ({ id: "e" + String(i).padStart(4, "0"), sourcePortId: `s${i}`, targetPortId: `t${i}`, kind: "incidence", minRankSpan: 1 })) });
  return makeProperGraph(source, ranks);
}
function randomSource(seed: number) { let state = seed; return () => { state = Math.imul(state, 1664525) + 1013904223 | 0; return (state >>> 0) / 4294967296; }; }
/** Quadratic crossing oracle deliberately does not use Fenwick, attachment
 * positions, pair costs, or an ordering implementation helper. */
function quadratic(edges: readonly BoundaryEdge[]): number {
  let answer = 0;
  for (let i = 0; i < edges.length; i++) for (let j = i + 1; j < edges.length; j++) {
    const a = edges[i]!, b = edges[j]!;
    if (a.source < b.source && a.target > b.target || a.source > b.source && a.target < b.target)
      answer += (a.weight ?? 1) * (b.weight ?? 1);
  }
  return answer;
}
function permutations(values: readonly number[]): number[][] {
  if (values.length < 2) return [[...values]];
  return values.flatMap((v, i) => permutations(values.filter((_, j) => i !== j)).map((tail) => [v, ...tail]));
}

describe("joint node and free-attachment swaps", () => {
  const run = (graph: ProperGraph, input: Ordering, trials = 256, constraints: readonly OrderConstraint[] = []) =>
    polishJointSwaps(graph, input, { trials, constraints, portSeparation: 8,
      proposePorts: (layers, ports, affected) => proposePortOrder(graph, layers, ports, 8, affected) });
  function fan(mode: PortSpec["mode"] = "free-on-side") {
    const graph = fixture([0, 2, 2, 2], [[0, 1], [0, 2], [0, 3]], mode);
    const layers = graph.layers.map((r) => [...r]); layers[2]!.reverse();
    return { graph, input: { layers, portOrder: { s0: 0, s1: 1, s2: 2 }, crossings: 3 },
      constraints: [[3, 2], [2, 1]] as const };
  }
  it("uncrosses a fan by moving its dummy tracks and source attachments together, revisiting earlier pairs", () => {
    const { graph, input, constraints } = fan();
    const before = JSON.stringify(input);
    const swapped = input.layers.map((r) => [...r]); swapped[1]!.reverse();
    // Moving tracks alone just transfers the three crossings to rank zero.
    expect(countCrossings(graph, swapped, input.portOrder)).toBe(3);
    const result = run(graph, input, 256, constraints);
    expect(result.ordering.crossings).toBe(0);
    expect(result.accepted).toBe(3);
    expect(result.exhausted).toBe(false);
    expect(result.ordering.layers[2]).toEqual(input.layers[2]);
    expect(result.ordering.portOrder.s2).toBeLessThan(result.ordering.portOrder.s1!);
    expect(result.ordering.portOrder.s1).toBeLessThan(result.ordering.portOrder.s0!);
    expect(JSON.stringify(input)).toBe(before);
    expect(run(graph, input, 256, constraints)).toEqual(result);
  });
  it.each(["fixed-order", "fixed-position"] as const)("preserves %s docks even when their crossings cannot be removed", (mode) => {
    const { graph, input, constraints } = fan(mode);
    const result = run(graph, input, 256, constraints);
    expect(result.accepted).toBe(0);
    expect(result.ordering.crossings).toBe(3);
    expect(portOffsets(graph.source, result.ordering.portOrder)).toEqual(portOffsets(graph.source, input.portOrder));
  });
  it("reports exhaustion and retains the last improvement under a strict trial budget", () => {
    const { graph, input, constraints } = fan();
    const zero = run(graph, input, 0, constraints);
    expect(zero).toMatchObject({ trials: 0, accepted: 0, exhausted: true });
    expect(zero.ordering).toEqual(input);
    const one = run(graph, input, 1, constraints);
    expect(one).toMatchObject({ trials: 1, accepted: 1, exhausted: true });
    expect(one.ordering.crossings).toBe(2);
  });
  it("agrees with the quadratic oracle and leaves no improving permitted adjacent joint move when completed", () => {
    const random = randomSource(874);
    for (let sample = 0; sample < 30; sample++) {
      const pairs: Pair[] = [];
      for (let u = 0; u < 6; u++) for (let v = u < 2 ? 2 : 6; v < (u < 2 ? 6 : 8); v++)
        if (random() < .6) pairs.push([u, v]);
      const graph = fixture([0, 0, 1, 1, 1, 1, 2, 2], pairs, "free-on-side");
      const input = { layers: graph.layers, portOrder: {}, crossings: countCrossings(graph, graph.layers) };
      const result = run(graph, input, 256);
      expect(result.exhausted).toBe(false);
      expect(result.ordering.crossings).toBeLessThanOrEqual(input.crossings);
      const positions = attachmentPositions(graph, result.ordering.layers, result.ordering.portOrder);
      const oracle = graph.segmentsByRank.reduce((total, segments) => total + quadratic(segments.map((s) => ({ source: positions.source[s]!, target: positions.target[s]! }))), 0);
      expect(result.ordering.crossings).toBe(oracle);
      expect(run(graph, result.ordering, 256).accepted).toBe(0);
    }
  });
});
function enumerateCosts(costs: readonly (readonly number[])[], constraints: readonly OrderConstraint[] = []): number {
  let optimum = Infinity;
  for (const p of permutations(costs.map((_, i) => i))) {
    if (constraints.some(([a, b]) => p.indexOf(a) >= p.indexOf(b))) continue;
    let cost = 0;
    for (let a = 0; a < p.length; a++) for (let b = a + 1; b < p.length; b++) cost += costs[p[a]!]![p[b]!]!;
    optimum = Math.min(optimum, cost);
  }
  return optimum;
}

describe("explicit proper layering", () => {
  it("calculates D before expansion and keeps original edge chains/semantic docks", () => {
    const graph = fixture([0, 1, 2, 4], [[0, 1], [1, 2], [2, 3], [0, 3], [0, 3]]);
    expect(graph.dummyCount).toBe(7);
    expect(graph.vertices).toHaveLength(11);
    graph.chains.forEach((chain, edgeIndex) => {
      expect(chain.length - 1).toBe(graph.vertices[chain.at(-1)!]!.rank - graph.vertices[chain[0]!]!.rank);
      for (let at = 1; at + 1 < chain.length; at++) expect(graph.vertices[chain[at]!]!).toMatchObject({ edgeIndex, chainOffset: at, width: 8, height: 0 });
      const segments = graph.segments.filter((s) => s.edgeIndex === edgeIndex);
      expect(segments[0]!.sourcePortId).toBe(graph.source.edges[edgeIndex]!.sourcePortId);
      expect(segments.at(-1)!.targetPortId).toBe(graph.source.edges[edgeIndex]!.targetPortId);
    });
    expect(graph.chains[3]!.slice(1, -1).some((v) => graph.chains[4]!.includes(v))).toBe(false);
    for (const s of graph.segments) expect(graph.vertices[s.target]!.rank - graph.vertices[s.source]!.rank).toBe(1);
  });
  it("diagnoses expansion limits, nonfinite/infeasible ranks and does not drop edges", () => {
    const graph = fixture([0, 1], [[0, 1]]);
    expect(() => makeProperGraph(graph.source, [0, 1_000_000], { expandedVertices: 100 })).toThrow(/expansion-budget/);
    expect(() => makeProperGraph(graph.source, [0, 4], { expandedVertices: 100, expandedSegments: 2 })).toThrow(/expansion-budget/);
    expect(() => makeProperGraph(graph.source, [0, 0])).toThrow(/proper-ranks/);
    expect(() => makeProperGraph(graph.source, [0, Infinity])).toThrow(/proper-ranks/);
    expect(() => makeProperGraph(graph.source, [0, 1], { dummyWidth: 0 })).toThrow(/dummy-clearance/);
    expect(makeProperGraph(normalizeGraph({ nodes: [], edges: [] }), [])).toMatchObject({ dummyCount: 0, layers: [], chains: [] });
  });
});

describe("port-aware bilayer Fenwick counting", () => {
  it("matches a quadratic oracle with equal endpoints, parallel incidences and weights", () => {
    const random = randomSource(76531);
    for (let sample = 0; sample < 500; sample++) {
      const edges = Array.from({ length: Math.floor(random() * 50) }, () => ({ source: Math.floor(random() * 10) - 5,
        target: Math.floor(random() * 10) - 5, weight: Math.floor(random() * 4) }));
      expect(countBoundaryCrossings(edges)).toBe(quadratic(edges));
      expect(countBoundaryCrossings([...edges].reverse())).toBe(quadratic(edges));
    }
    expect(countBoundaryCrossings([{ source: 0, target: 2 }, { source: 0, target: 1 }, { source: 1, target: 1 }])).toBe(1);
    expect(countBoundaryCrossings([{ source: 0, target: 1 }, { source: 0, target: 1 }])).toBe(0);
  });
  it("counts large values exactly above 32-bit range and diagnoses unsafe arithmetic", () => {
    expect(countBoundaryCrossings([{ source: 0, target: 1, weight: 100000 }, { source: 1, target: 0, weight: 100000 }])).toBe(10_000_000_000);
    expect(() => countBoundaryCrossings([{ source: 0, target: 1, weight: 100_000_000 }, { source: 1, target: 0, weight: 100_000_000 }])).toThrow(/crossing-capacity/);
    expect(() => countBoundaryCrossings([{ source: Infinity, target: 1 }])).toThrow(/crossing-input/);
  });
  it("uses distinct fixed docks and excludes only equal actual boundary endpoints", () => {
    const graph = fixture([0, 1], [[0, 1], [0, 1]]);
    const nodes = graph.source.nodes.map((n, index) => index ? { ...n, ports: n.ports.map((p, i) => ({ ...p, offset: { x: i ? 16 : 24, y: 24 } })) } : n);
    const crossed = makeProperGraph(normalizeGraph({ ...graph.source, nodes }), [0, 1]);
    expect(countCrossings(crossed, crossed.layers)).toBe(1);
    const shared = { ...nodes[0]!, ports: nodes[0]!.ports.map((p) => ({ ...p, offset: { x: 16, y: 0 } })) };
    const equal = makeProperGraph(normalizeGraph({ ...graph.source, nodes: [shared, nodes[1]!] }), [0, 1]);
    expect(countCrossings(equal, equal.layers)).toBe(0);
    const positions = attachmentPositions(crossed, crossed.layers);
    const offsets = portOffsets(crossed.source);
    expect(positions.source[0]).toBe(offsets.s0!.x / crossed.source.nodes[0]!.width);
    expect(positions.target[0]).toBe(offsets.t0!.x / crossed.source.nodes[1]!.width);
  });
  it("scores BOTH boundaries when moving an internal-layer vertex", () => {
    const graph = fixture([0, 0, 1, 1, 2, 2], [[0, 3], [1, 2], [2, 5], [3, 4]]);
    const positions = attachmentPositions(graph, graph.layers);
    expect(orderedPairCost(graph, positions, 2, 3)).toBe(2);
    expect(orderedPairCost(graph, positions, 3, 2)).toBe(0);
    const swapped = graph.layers.map((row, rank) => rank === 1 ? [...row].reverse() : row);
    expect(countCrossings(graph, graph.layers) - countCrossings(graph, swapped)).toBe(2);
    expect(() => attachmentPositions(graph, [graph.layers[0]!, graph.layers[1]!])).toThrow(/layer-permutation/);
  });
});

describe("exact subset ordering", () => {
  it("matches permutation enumeration with deterministic ties and hard prefixes", () => {
    const random = randomSource(6247);
    for (let k = 0; k <= 7; k++) for (let sample = 0; sample < 12; sample++) {
      const costs = Array.from({ length: k }, (_, u) => Array.from({ length: k }, (_, v) => u === v ? 0 : Math.floor(random() * 7)));
      const constraints: OrderConstraint[] = [];
      for (let a = 0; a < k; a++) for (let b = a + 1; b < k; b++) if (random() < 0.15) constraints.push([a, b]);
      const answer = subsetOrder(costs, constraints);
      expect(answer.cost).toBe(enumerateCosts(costs, constraints));
      expect(answer).toEqual(subsetOrder(costs, constraints));
      for (const [a, b] of constraints) expect(answer.order.indexOf(a)).toBeLessThan(answer.order.indexOf(b));
      expect(answer.termination).toBe("optimal-for-fixed-neighbors");
      expect(answer.states).toBeLessThanOrEqual(2 ** k);
    }
  });
  it("solves k=16 within the direct memory budget and labels budget fallbacks", () => {
    const costs = Array.from({ length: 16 }, (_, u) => Array.from({ length: 16 }, (_, v) => u < v ? 0 : 1));
    const answer = subsetOrder(costs);
    expect(answer.cost).toBe(0); expect(answer.order).toEqual(Array.from({ length: 16 }, (_, i) => i)); expect(answer.states).toBe(65536);
    expect(subsetOrder(costs, [], { stateBudget: 100 })).toMatchObject({ states: 0, termination: "budget-exhausted" });
    expect(subsetOrder(costs, [], { maxVertices: 12 }).termination).toBe("layer-too-wide");
    expect(() => subsetOrder([[0, 1], [1, 0]], [[0, 1], [1, 0]])).toThrow(/cyclic-order-constraint/);
  });
  it("matches full two-boundary crossing enumeration including constant fixed-dock terms", () => {
    const graph = fixture([0, 0, 0, 1, 1, 1, 1, 2, 2, 2], [[0, 3], [0, 5], [1, 3], [1, 4], [2, 6], [2, 4], [3, 8], [4, 9], [5, 7], [6, 8], [3, 7], [3, 7]]);
    const ordering: Ordering = { layers: graph.layers, portOrder: {}, crossings: countCrossings(graph, graph.layers) };
    const result = exactLayerOrder(graph, ordering, 1);
    let oracle = Infinity;
    for (const row of permutations(graph.layers[1]!)) oracle = Math.min(oracle, countCrossings(graph, [graph.layers[0]!, row, graph.layers[2]!]));
    expect(countCrossings(graph, [graph.layers[0]!, result.order, graph.layers[2]!])).toBe(oracle);
    const positions = attachmentPositions(graph, graph.layers), costs = layerPairCosts(graph, positions, graph.layers[1]!);
    expect(result.cost).toBe(enumerateCosts(costs));
  });
  it("keeps outside-window pair terms constant and preserves constraints", () => {
    const graph = fixture([0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2], [[0, 4], [0, 6], [1, 5], [1, 8], [2, 3], [2, 7], [3, 10], [4, 9], [5, 10], [6, 9], [7, 10], [8, 9]]);
    const ordering = { layers: graph.layers, portOrder: {}, crossings: countCrossings(graph, graph.layers) };
    const result = exactLayerOrder(graph, ordering, 1, { start: 1, length: 4, constraints: [[4, 6]] });
    expect(result.order[0]).toBe(3); expect(result.order.at(-1)).toBe(8);
    let oracle = Infinity;
    for (const window of permutations([4, 5, 6, 7])) if (window.indexOf(4) < window.indexOf(6)) oracle = Math.min(oracle, countCrossings(graph, [graph.layers[0]!, [3, ...window, 8], graph.layers[2]!]));
    expect(countCrossings(graph, [graph.layers[0]!, result.order, graph.layers[2]!])).toBe(oracle);
  });
});

describe("bounded deterministic ordering portfolio", () => {
  it("draws clean paths/diamonds and never deletes unavoidable dense incidences", () => {
    for (const graph of [fixture([0, 1, 2], [[0, 1], [1, 2]]), fixture([0, 1, 1, 2], [[0, 1], [0, 2], [1, 3], [2, 3]])]) {
      const search = orderGraph(graph);
      expect(search.orderings[0]!.crossings).toBe(0);
      expect(search.orderings[0]!.layers.flat().sort((a, b) => a - b)).toEqual(graph.vertices.map((v) => v.index));
    }
    const complete = fixture([0, 0, 0, 1, 1, 1], Array.from({ length: 3 }, (_, u) => Array.from({ length: 3 }, (_, v): Pair => [u, v + 3])).flat());
    const search = orderGraph(complete);
    expect(search.orderings[0]!.crossings).toBeGreaterThan(0); expect(complete.chains).toHaveLength(9);
  });
  // Runs 25 deterministic fixtures twice and checks their operation caps.
  // The emergency test timeout allows concurrent browser/CI load; it is not
  // a production search budget or a throughput assertion.
  it("preserves hard ordering and compares entire states after exploratory sweeps", () => {
    const random = randomSource(7173);
    for (let sample = 0; sample < 25; sample++) {
      const pairs: Pair[] = [];
      for (let u = 0; u < 9; u++) for (let v = Math.floor(u / 3) * 3 + 3; v < Math.min(12, Math.floor(u / 3) * 3 + 6); v++) if (random() < 0.55) pairs.push([u, v]);
      const graph = fixture(Array.from({ length: 12 }, (_, i) => Math.floor(i / 3)), pairs);
      const initial = countCrossings(graph, graph.layers), constraints: OrderConstraint[] = [[3, 5]], options = { sweeps: 3, siftingMoves: 200, dpStates: 1000, constraints };
      const result = orderGraph(graph, options);
      expect(result.orderings[0]!.crossings).toBeLessThanOrEqual(initial);
      expect(result).toEqual(orderGraph(graph, options));
      for (const order of result.orderings) {
        expect(order.crossings).toBe(countCrossings(graph, order.layers, order.portOrder));
        expect(order.layers[1]!.indexOf(3)).toBeLessThan(order.layers[1]!.indexOf(5));
      }
      expect(result.stats.siftingMoves).toBeLessThanOrEqual(200 * 4);
      expect(result.stats.dpStates).toBeLessThanOrEqual(1000 * 4);
    }
  }, 30_000);
  it("optimizes free incidence orders without changing fixed positions or dock identities", () => {
    const graph = fixture([0, 1, 1, 1], [[0, 3], [0, 1], [0, 2]], "free-on-side");
    const proposed = proposePortOrder(graph, graph.layers, { s0: 0, s1: 1, s2: 2 });
    expect(proposed.s1).toBeLessThan(proposed.s2!); expect(proposed.s2).toBeLessThan(proposed.s0!);
    expect(countCrossings(graph, graph.layers, proposed)).toBe(0);
    const constrainedNodes = graph.source.nodes.map((node, index): MeasuredNode => index ? node : { ...node, ports: node.ports.map((p) => p.id === "s0" || p.id === "s1" ? { ...p, mode: "fixed-order", order: p.id === "s0" ? 0 : 1 } : p) });
    const constrained = makeProperGraph(normalizeGraph({ ...graph.source, nodes: constrainedNodes }), [0, 1, 1, 1]);
    const result = orderGraph(constrained);
    for (const order of result.orderings) {
      const offsets = portOffsets(constrained.source, order.portOrder);
      expect(offsets.s0!.x).toBeLessThan(offsets.s1!.x);
      expect(constrained.source.nodes[0]!.ports.find((p) => p.id === "s0")!.semanticEndpointId).toBe("statement:0:0");
    }
  });
  it("ignores input JSON ordering and decoration that does not change measurements", () => {
    const graph = fixture([0, 1, 1, 2], [[0, 1], [0, 2], [1, 3], [2, 3], [0, 3]]);
    const decorated = normalizeGraph({ nodes: [...graph.source.nodes].reverse().map((node) => ({ ...node, status: "other", color: "blue" })), edges: [...graph.source.edges].reverse() });
    const ranked = rankGraph(graph.source), repeat = rankGraph(decorated);
    expect(orderGraph(makeProperGraph(graph.source, ranked.ranks))).toEqual(orderGraph(makeProperGraph(decorated, repeat.ranks)));
  });
});
