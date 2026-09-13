import fs from "node:fs";
import { describe, expect, it } from "vitest";
import { layoutGraph } from "../src/graph-layout/index.js";
import { orderGraph } from "../src/graph-layout/order-heuristic.js";
import { portOffsets } from "../src/graph-layout/ports.js";
import { makeProperGraph, type ProperGraph } from "../src/graph-layout/proper-graph.js";
import { rankGraph } from "../src/graph-layout/rank-simplex.js";
import { DEFAULT_PROFILE, type MeasuredGraph } from "../src/graph-layout/types.js";
import { validateGeometry } from "../src/graph-layout/validate.js";

const fixtures = (JSON.parse(fs.readFileSync(new URL("./fixtures/graph-layout/tuning-order-regressions.json", import.meta.url), "utf8")) as {
  fixtures: { id: string; graph: MeasuredGraph; minimumCrossings: number }[];
}).fixtures;
// The fixed measured oracle fixtures predate the wider production spacing.
const profile = { ...DEFAULT_PROFILE, id: "readable-v1", portSeparation: 8, dummyGap: 8, nodeGap: 28 };
function proper(graph: MeasuredGraph): ProperGraph {
  const connected = { ...graph, nodes: graph.nodes.filter((node) => node.ports.length) };
  return makeProperGraph(connected, rankGraph(connected).ranks);
}
function* permutations<T>(items: readonly T[]): Generator<T[]> {
  if (!items.length) { yield []; return; }
  for (let i = 0; i < items.length; i++) for (const suffix of permutations(items.filter((_, j) => j !== i))) yield [items[i]!, ...suffix];
}
/** Independent quadratic oracle for freely assignable north/south ports.
 * Shared node endpoints add no crossings because their ports can follow the
 * opposite node order; distinct incidences remain in the segment arrays. */
function freeCrossings(graph: ProperGraph, layers: readonly (readonly number[])[]): number {
  const positions = new Map(layers.flatMap((row) => row.map((v, i) => [v, i] as const)));
  let count = 0;
  for (const boundary of graph.segmentsByRank) for (let i = 0; i < boundary.length; i++) for (let j = i + 1; j < boundary.length; j++) {
    const a = graph.segments[boundary[i]!]!, b = graph.segments[boundary[j]!]!;
    if ((positions.get(a.source)! - positions.get(b.source)!) * (positions.get(a.target)! - positions.get(b.target)!) < 0) count++;
  }
  return count;
}
/** Enumerate all left permutations and independently solve the right subset
 * recurrence. Outer boundaries share their single source/target, so their
 * free-port optimum is zero for every choice of the two middle orders. */
function twoMiddleLayerOracle(graph: ProperGraph) {
  expect(graph.layers.map((row) => row.length)).toEqual([1, 6, 8, 1]);
  const left = graph.layers[1]!, right = graph.layers[2]!;
  let minimum = Infinity, permutationsTried = 0, states = 0;
  for (const order of permutations(left)) {
    permutationsTried++;
    const position = new Map(order.map((v, i) => [v, i] as const));
    const cost = right.map((u) => right.map((v) => {
      let count = 0;
      for (const a of graph.incoming[u]!) for (const b of graph.incoming[v]!)
        if (position.get(graph.segments[a]!.source)! > position.get(graph.segments[b]!.source)!) count++;
      return count;
    }));
    const size = 1 << right.length, values = new Float64Array(size).fill(Infinity), appended = new Uint8Array(size);
    values[0] = 0;
    for (let mask = 1; mask < size; mask++) {
      states++;
      for (let v = 0; v < right.length; v++) if (mask & 1 << v) {
        const rest = mask ^ 1 << v; let candidate = values[rest]!;
        for (let u = 0; u < right.length; u++) if (rest & 1 << u) candidate += cost[u]![v]!;
        if (candidate < values[mask]!) { values[mask] = candidate; appended[mask] = v; }
      }
    }
    const reverse: number[] = [];
    for (let mask = size - 1; mask; ) { const v = appended[mask]!; reverse.push(right[v]!); mask ^= 1 << v; }
    expect(freeCrossings(graph, [graph.layers[0]!, order, reverse.reverse(), graph.layers[3]!])).toBe(values[size - 1]);
    minimum = Math.min(minimum, values[size - 1]!);
  }
  return { minimum, permutationsTried, states };
}
/** The last rank has one parent per node, hence can always have zero crossings.
 * Middle nodes with identical incoming neighbor sets are twins: each has the
 * same pair cost with every outsider. Moving all members to the better of two
 * positions cannot worsen that cost, while their internal cost is constant.
 * Therefore an optimum exists with contiguous twin blocks. Enumerating all
 * four-source and five-block orders proves a bound without merging incidences. */
function twinBlockOracle(graph: ProperGraph) {
  expect(graph.layers.map((row) => row.length)).toEqual([4, 24, 8]);
  expect(graph.layers[2]!.every((v) => graph.incoming[v]!.length === 1)).toBe(true);
  const groups = new Map<string, number[]>();
  for (const v of graph.layers[1]!) {
    const key = graph.incoming[v]!.map((e) => graph.segments[e]!.source).sort((a, b) => a - b).join(",");
    const members = groups.get(key) ?? []; members.push(v); groups.set(key, members);
  }
  expect([...groups.values()].map((group) => group.length).sort((a, b) => a - b)).toEqual([1, 3, 3, 6, 11]);
  let minimum = Infinity, permutationsTried = 0;
  for (const left of permutations(graph.layers[0]!)) for (const blocks of permutations([...groups.values()])) {
    permutationsTried++;
    const middle = blocks.flat(), positions = new Map(middle.map((v, i) => [v, i] as const));
    const right = [...graph.layers[2]!].sort((a, b) => positions.get(graph.segments[graph.incoming[a]![0]!]!.source)! - positions.get(graph.segments[graph.incoming[b]![0]!]!.source)!);
    minimum = Math.min(minimum, freeCrossings(graph, [left, middle, right]));
  }
  return { minimum, permutationsTried };
}

describe("bounded escape from alternating node/port local minima", () => {
  // Exhausts 720 permutations and 183,600 oracle states before full layout.
  // Keep an emergency test timeout for concurrent browser/CI load while the
  // production operation budgets and every oracle assertion remain fixed.
  it("matches the independent 6! × subset oracle on the complete Lax12 tuning topology", () => {
    const fixture = fixtures[0]!, graph = proper(fixture.graph);
    expect(twoMiddleLayerOracle(graph)).toEqual({ minimum: 1, permutationsTried: 720, states: 183600 });
    const result = layoutGraph(fixture.graph, { inputDigest: fixture.id, profile });
    expect(result.metrics.crossings).toBe(fixture.minimumCrossings);
    expect(validateGeometry(fixture.graph, result.geometry).diagnostics).toEqual([]);
    expect(result.geometry.edges).toHaveLength(19);
  }, 30_000);

  it("matches the independent twin-block bound with all 39 Lax916827 incidences retained", () => {
    const fixture = fixtures[1]!, graph = proper(fixture.graph);
    expect(twinBlockOracle(graph)).toEqual({ minimum: 9, permutationsTried: 2880 });
    const result = layoutGraph(fixture.graph, { inputDigest: fixture.id, profile });
    expect(result.metrics.crossings).toBe(fixture.minimumCrossings);
    expect(validateGeometry(fixture.graph, result.geometry).diagnostics).toEqual([]);
    expect(result.geometry.nodes).toHaveLength(39);
    expect(result.geometry.edges).toHaveLength(39);
  });

  it("respects whole-layer constraints, fixed port order and remaining work budgets", () => {
    const original = fixtures[0]!.graph;
    const graph = proper({ ...original, nodes: original.nodes.map((node) => node.ports.length === 5 && node.ports.every((port) => port.side === "north")
      ? { ...node, ports: node.ports.map((port, order) => ({ ...port, mode: "fixed-order", order })) } : node) });
    const constraints = [[graph.layers[1]![0]!, graph.layers[1]![3]!], [graph.layers[2]![2]!, graph.layers[2]![1]!]] as const;
    const before = JSON.stringify(graph.layers);
    const options = { sweeps: 0, siftingMoves: 1000, dpStates: 100_000, exactLayerLimit: 16, seeds: [0], constraints };
    const result = orderGraph(graph, options);
    expect(result.stats.permutationTrials).toBeGreaterThan(0);
    expect(result.stats.siftingMoves + result.stats.permutationTrials).toBeLessThanOrEqual(options.siftingMoves);
    expect(result.stats.dpStates).toBeLessThanOrEqual(options.dpStates);
    expect(JSON.stringify(graph.layers)).toBe(before);
    for (const ordering of result.orderings) {
      for (const [u, v] of constraints) {
        const row = ordering.layers[graph.vertices[u]!.rank]!;
        expect(row.indexOf(u)).toBeLessThan(row.indexOf(v));
      }
      const offsets = portOffsets(graph.source, ordering.portOrder);
      for (const node of graph.source.nodes) {
        const fixed = node.ports.filter((port) => port.mode === "fixed-order").sort((a, b) => a.order! - b.order!);
        for (let i = 1; i < fixed.length; i++) expect(offsets[fixed[i - 1]!.id]!.x).toBeLessThan(offsets[fixed[i]!.id]!.x);
      }
    }
    const exhausted = orderGraph(graph, { ...options, siftingMoves: 0, dpStates: 0 });
    expect(exhausted.stats.permutationTrials).toBe(0);
    expect(exhausted.stats.dpStates).toBe(0);
  });
});
