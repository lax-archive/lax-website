import { describe, expect, it } from "vitest";
import { condensation, stronglyConnectedComponents, topologicalOrder, weakComponents } from "../src/graph-layout/components.js";
import { assertFeasibleRanks, longestPathRanks, rankIndexed, type RankEdge } from "../src/graph-layout/rank-simplex.js";

const edge = (source: number, target: number, minRankSpan = 1, weight = 1): RankEdge => ({ id: `${source}:${target}`, source, target, minRankSpan, weight });

/** Independent bounded enumeration, without calling the ranker's feasibility
 * or objective helpers. DAG fixtures use integer labels in topological order. */
function enumerateRankObjective(n: number, edges: readonly RankEdge[], bound: number): number {
  const values: number[] = [], incoming = Array.from({ length: n }, (_, v) => edges.filter((e) => e.target === v));
  let best = Infinity;
  const visit = (v: number) => {
    if (v === n) {
      let objective = 0;
      for (const e of edges) objective += (e.weight ?? 1) * (values[e.target]! - values[e.source]!);
      best = Math.min(best, objective); return;
    }
    for (let value = 0; value <= bound; value++) {
      if (incoming[v]!.some((e) => value - values[e.source]! < e.minRankSpan)) continue;
      values[v] = value; visit(v + 1);
    }
  };
  visit(0); return best;
}
function seeded(seed: number): () => number { let state = seed; return () => { state = Math.imul(state, 1664525) + 1013904223 | 0; return (state >>> 0) / 4294967296; }; }

describe("iterative component algorithms", () => {
  it("retains all parallel incidences and neutral display SCC membership", () => {
    const edges = [edge(0, 1), edge(1, 0), edge(1, 2), { ...edge(1, 2), id: "parallel" }, edge(2, 3)].map((e, index) => ({ ...e, index, weight: e.weight! }));
    expect(weakComponents(5, edges)).toEqual([[0, 1, 2, 3], [4]]);
    expect(stronglyConnectedComponents(5, edges)).toEqual([[0, 1], [2], [3], [4]]);
    const condensed = condensation(5, edges);
    expect(condensed.internalEdges).toEqual([[0, 1], [], [], []]);
    expect(condensed.edges.map((e) => e.originalEdgeIndex)).toEqual([2, 3, 4]);
    expect(topologicalOrder(4, condensed.edges)).toEqual([0, 1, 2, 3]);
    expect(() => topologicalOrder(5, edges)).toThrow(/cyclic-rank-input/);
    expect(() => topologicalOrder(1, [edge(0, 0)])).toThrow(/cyclic-rank-input/);
  });
  it("does not recurse on a 30000-node chain or strongly connected ring", () => {
    const n = 30000, chain = Array.from({ length: n - 1 }, (_, i) => edge(i, i + 1));
    expect(topologicalOrder(n, chain)).toEqual(Array.from({ length: n }, (_, i) => i));
    expect(stronglyConnectedComponents(n, [...chain, edge(n - 1, 0)])).toHaveLength(1);
    expect(weakComponents(n, chain)).toHaveLength(1);
  });
  it("handles empty input and rejects endpoints before indexing", () => {
    expect(topologicalOrder(0, [])).toEqual([]);
    expect(stronglyConnectedComponents(0, [])).toEqual([]);
    expect(() => weakComponents(2, [edge(0, 2)])).toThrow(/missing-endpoint/);
  });
});

describe("feasible tight-tree network-simplex ranks", () => {
  it("matches exhaustive optima for all 1024 labeled five-node unit-span DAGs", () => {
    const possible: RankEdge[] = [];
    for (let u = 0; u < 5; u++) for (let v = u + 1; v < 5; v++) possible.push(edge(u, v));
    for (let mask = 0; mask < 1 << possible.length; mask++) {
      const edges = possible.filter((_, e) => mask & 1 << e), result = rankIndexed(5, edges, { debug: true });
      expect(result.objective, `edge mask ${mask}`).toBe(enumerateRankObjective(5, edges, 4));
      expect(result.termination).toBe("optimal-for-rank-objective");
    }
  });
  it("matches mixed-span, weighted and zero-weight exhaustive oracles", () => {
    const random = seeded(0x1234);
    for (let sample = 0; sample < 150; sample++) {
      const edges: RankEdge[] = [];
      for (let u = 0; u < 4; u++) for (let v = u + 1; v < 4; v++) if (random() < 0.7) edges.push(edge(u, v, 1 + Math.floor(3 * random()), Math.floor(4 * random())));
      const result = rankIndexed(4, edges, { debug: true });
      expect(result.objective, `sample ${sample}`).toBe(enumerateRankObjective(4, edges, 9));
      expect(result.objective).toBeLessThanOrEqual(result.initialObjective);
    }
  });
  it("supports signed lower bounds for auxiliary coordinate DAGs", () => {
    const random = seeded(61);
    for (let sample = 0; sample < 100; sample++) {
      const edges: RankEdge[] = [];
      for (let u = 0; u < 4; u++) for (let v = u + 1; v < 4; v++) if (random() < 0.8) edges.push(edge(u, v, Math.floor(7 * random()) - 3, Math.floor(4 * random())));
      const result = rankIndexed(4, edges, { debug: true });
      expect(result.objective, `signed sample ${sample}`).toBe(enumerateRankObjective(4, edges, 9));
    }
  });
  it("handles diamonds, paths, isolated vertices, parallel constraints and determinism", () => {
    const edges = [edge(0, 1, 3), edge(0, 2, 1), edge(1, 3, 2), edge(2, 3, 3), { ...edge(0, 1, 2), id: "parallel" }];
    const first = rankIndexed(5, edges, { debug: true });
    expect(first).toEqual(rankIndexed(5, [...edges].reverse(), { debug: true }));
    expect(first.ranks[4]).toBe(0);
    expect(first.objective).toBe(enumerateRankObjective(5, edges, 8));
    const path = [edge(0, 1, 2), edge(1, 2, 3), edge(2, 3, 1)];
    expect(rankIndexed(4, path).ranks).toEqual([0, 2, 5, 6]);
    expect(rankIndexed(0, []).ranks).toEqual([]);
    expect(rankIndexed(1, []).ranks).toEqual([0]);
  });
  it("maintains feasibility through degenerate pivots and reports exhausted budgets honestly", () => {
    const random = seeded(19283); let zeroPivots = 0, pivots = 0, exhausted = 0;
    for (let sample = 0; sample < 300; sample++) {
      const edges: RankEdge[] = [];
      for (let u = 0; u < 9; u++) for (let v = u + 1; v < 9; v++) if (random() < 0.35) edges.push(edge(u, v, 1 + Math.floor(3 * random()), Math.floor(3 * random())));
      const full = rankIndexed(9, edges, { debug: true, onPivot: (s) => {
        for (const e of s.edges) expect(s.ranks[e.target]! - s.ranks[e.source]!).toBeGreaterThanOrEqual(e.minRankSpan);
        for (const i of s.treeEdgeIndexes) { const e = s.edges[i]!; expect(s.ranks[e.target]! - s.ranks[e.source]!).toBe(e.minRankSpan); }
      } });
      pivots += full.pivots; zeroPivots += full.zeroPivots;
      const capped = rankIndexed(9, edges, { pivotBudget: 0, debug: true });
      if (capped.termination === "budget-exhausted") exhausted++;
      assertFeasibleRanks(9, edges, capped.ranks);
      expect(capped.objective).toBeGreaterThanOrEqual(full.objective);
      expect(capped.objective).toBeLessThanOrEqual(capped.initialObjective);
    }
    expect(pivots).toBeGreaterThan(0); expect(zeroPivots).toBeGreaterThan(0); expect(exhausted).toBeGreaterThan(0);
  });
  it("preserves component-internal ranks when another component is added", () => {
    const edges = [edge(0, 1), edge(1, 2), edge(3, 2), edge(3, 4), edge(4, 5)];
    const a = rankIndexed(6, edges, { pivotBudget: 1 }), b = rankIndexed(8, [...edges, edge(6, 7)], { pivotBudget: 1 });
    expect(b.ranks.slice(0, 6)).toEqual(a.ranks);
  });
  it("rejects cyclic DAG assumptions and arithmetic that cannot remain exact", () => {
    expect(() => rankIndexed(2, [edge(0, 1), edge(1, 0)])).toThrow(/cyclic-rank-input/);
    expect(() => rankIndexed(3, [edge(0, 1, Number.MAX_SAFE_INTEGER), edge(1, 2)])).toThrow(/rank-arithmetic/);
    expect(() => rankIndexed(2, [edge(0, 1, 2, Number.MAX_SAFE_INTEGER)])).toThrow(/rank-arithmetic/);
    expect(() => rankIndexed(2, [edge(0, 1, 1, -1)])).toThrow(/rank-constraint/);
    expect(longestPathRanks(3, [edge(0, 1, 3), edge(1, 2, 5), edge(0, 2)])).toEqual([0, 3, 8]);
  });
});
