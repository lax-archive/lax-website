import { expect, it } from "vitest";
import { dummyGaps, polishChains } from "../src/graph-layout/order-chain.js";
import { countCrossings } from "../src/graph-layout/cross-count.js";
import { makeProperGraph } from "../src/graph-layout/proper-graph.js";
import { normalizeGraph } from "../src/graph-layout/normalize.js";
import type { MeasuredGraph } from "../src/graph-layout/types.js";

function fixture() {
  const pairs = [[0, 2], [1, 3], [2, 4], [3, 5], [4, 6], [5, 7], [0, 7], [1, 6]];
  const source: MeasuredGraph = { nodes: Array.from({ length: 8 }, (_, v) => ({ id: String(v), kind: "concept", width: 56, height: 24, labelBoxes: [],
    ports: pairs.flatMap(([u, w], e) => [
      ...(u === v ? [{ id: e + "s", nodeId: String(v), semanticEndpointId: String(v), side: "north" as const, mode: "free-on-side" as const }] : []),
      ...(w === v ? [{ id: e + "t", nodeId: String(v), semanticEndpointId: String(v), side: "south" as const, mode: "free-on-side" as const }] : []),
    ]) })), edges: pairs.map((_, e) => ({ id: String(e), sourcePortId: e + "s", targetPortId: e + "t", kind: "import", minRankSpan: 1 })) };
  return makeProperGraph(normalizeGraph(source), [0, 0, 1, 1, 2, 2, 3, 3]);
}
it("scores coherent long-chain moves across all boundaries within a fixed cap", () => {
  const graph = fixture(), layers = graph.layers.map((row, rank) => rank % 2 ? [...row].reverse() : [...row]);
  const initial = { layers, portOrder: {}, crossings: countCrossings(graph, layers) };
  const result = polishChains(graph, initial, { moves: 7, constraints: [[0, 1]] });
  expect(result.moves).toBe(7);
  expect(result.ordering.crossings).toBeLessThanOrEqual(initial.crossings);
  expect(result.ordering.crossings).toBe(countCrossings(graph, result.ordering.layers));
  expect(result.ordering.layers[0]!.indexOf(0)).toBeLessThan(result.ordering.layers[0]!.indexOf(1));
  result.ordering.layers.forEach((row, rank) => expect([...row].sort((a, b) => a - b)).toEqual([...layers[rank]!].sort((a, b) => a - b)));
  expect(polishChains(graph, initial, { moves: 7, constraints: [[0, 1]] })).toEqual(result);
  expect(polishChains(graph, initial, { moves: 0 }).ordering).toEqual(initial);
});
it("counts only internal runs of dummies, not left or right gutters", () => {
  const graph = fixture(), dummies = graph.layers[1]!.filter((v) => graph.vertices[v]!.nodeIndex === undefined);
  expect(dummyGaps(graph, [[dummies[0]!, 2, 3, dummies[1]!]])).toBe(0);
  expect(dummyGaps(graph, [[2, ...dummies, 3]])).toBe(1);
});
