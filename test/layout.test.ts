import fs from "node:fs";
import { performance } from "node:perf_hooks";
import vm from "node:vm";
import { describe, expect, it } from "vitest";

type Node = { id: string; width: number };
type Edge = { from: string; to: string };
type Point = { x: number; layer: number };
type Layout = {
  positions: Map<string, Point>;
  routes: Point[][];
  rankRoutes: Point[][];
  crossings: number;
  maxPairCrossings: number;
  width: number;
};

const context: Record<string, unknown> = {};
vm.createContext(context);
vm.runInContext(fs.readFileSync("assets/site/layout.js", "utf8"), context);
const layoutDag = (context.laxLayout as { layoutDag(input: {
  nodes: Node[];
  edges: Edge[];
  nodeGap?: number;
  alignEdgeIndices?: number[];
}): Layout }).layoutDag;

function serialize(layout: Layout) {
  return {
    positions: [...layout.positions].map(([id, point]) => [id, point.x, point.layer]),
    routes: layout.routes,
    rankRoutes: layout.rankRoutes,
    crossings: layout.crossings,
    maxPairCrossings: layout.maxPairCrossings,
    width: layout.width,
  };
}

function xAt(points: Point[], layer: number): number {
  const exact = points.find((point) => point.layer === layer);
  if (exact) return exact.x;
  const upperIndex = points.findIndex((point) => point.layer > layer);
  const lower = points[upperIndex - 1]!;
  const upper = points[upperIndex]!;
  const fraction = (layer - lower.layer) / (upper.layer - lower.layer);
  return lower.x + (upper.x - lower.x) * fraction;
}

function pairCrossings(layout: Layout, edges: Edge[], first: number, second: number): number {
  const firstPoints = [layout.positions.get(edges[first]!.from)!, ...layout.routes[first]!,
    layout.positions.get(edges[first]!.to)!];
  const secondPoints = [layout.positions.get(edges[second]!.from)!, ...layout.routes[second]!,
    layout.positions.get(edges[second]!.to)!];
  const start = Math.max(firstPoints[0]!.layer, secondPoints[0]!.layer);
  const end = Math.min(firstPoints.at(-1)!.layer, secondPoints.at(-1)!.layer);
  let crossings = 0;
  for (let layer = start; layer < end; layer += 1) {
    const sharedLower = edges[first]!.from === edges[second]!.from &&
      layer === firstPoints[0]!.layer && layer === secondPoints[0]!.layer;
    const sharedUpper = edges[first]!.to === edges[second]!.to &&
      layer + 1 === firstPoints.at(-1)!.layer && layer + 1 === secondPoints.at(-1)!.layer;
    if (sharedLower || sharedUpper) continue;
    const lower = xAt(firstPoints, layer) - xAt(secondPoints, layer);
    const upper = xAt(firstPoints, layer + 1) - xAt(secondPoints, layer + 1);
    if (lower * upper < -1e-6) crossings += 1;
  }
  return crossings;
}

describe("Sugiyama graph layout", () => {
  it("minimizes a reversible two-rank crossing set deterministically", () => {
    const nodes = ["a", "b", "c", "x", "y", "z"].map((id) => ({ id, width: 36 }));
    const edges = [
      { from: "a", to: "z" },
      { from: "b", to: "y" },
      { from: "c", to: "x" },
    ];
    const first = layoutDag({ nodes, edges });
    const second = layoutDag({ nodes, edges });
    expect(first.crossings).toBe(0);
    expect(first.maxPairCrossings).toBe(0);
    expect(serialize(first)).toEqual(serialize(second));
  });

  it("escapes a one-sided local minimum instead of keeping avoidable crossings", () => {
    const nodes = [
      ...Array.from({ length: 5 }, (_, index) => `a${index}`),
      ...Array.from({ length: 5 }, (_, index) => `z${index}`),
    ].map((id) => ({ id, width: 30 }));
    const pairs = [
      [0, 0], [0, 1], [0, 3], [0, 4], [1, 2], [2, 1],
      [2, 2], [2, 3], [3, 0], [3, 1], [3, 4], [4, 1],
    ];
    const edges = pairs.map(([from, to]) => ({ from: `a${from}`, to: `z${to}` }));

    // Exhausting both five-vertex rank permutations gives an optimum of five;
    // the former median/transpose heuristic stopped at eight.
    expect(layoutDag({ nodes, edges }).crossings).toBe(5);
  });

  it("never lets a pair of long edges cross more than once", () => {
    const ids = Array.from({ length: 4 }, (_, layer) =>
      Array.from({ length: 4 }, (__, column) => `${String.fromCharCode(97 + column)}${layer}`)).flat();
    const nodes = ids.map((id) => ({ id, width: 34 }));
    const edges: Edge[] = [];
    for (let layer = 0; layer < 3; layer += 1)
      for (let column = 0; column < 4; column += 1)
        edges.push({
          from: `${String.fromCharCode(97 + column)}${layer}`,
          to: `${String.fromCharCode(97 + column)}${layer + 1}`,
        });
    edges.push(
      { from: "a0", to: "d3" },
      { from: "d0", to: "a3" },
      { from: "b0", to: "c3" },
      { from: "c0", to: "b3" },
      { from: "a0", to: "c2" },
      { from: "d1", to: "b3" },
    );
    const layout = layoutDag({ nodes, edges });
    expect(layout.maxPairCrossings).toBeLessThanOrEqual(1);
    for (let first = 0; first < edges.length; first += 1)
      for (let second = first + 1; second < edges.length; second += 1)
        expect(pairCrossings(layout, edges, first, second), `${first}/${second}`)
          .toBeLessThanOrEqual(1);
    edges.forEach((edge, edgeIndex) => {
      const sourceLayer = layout.positions.get(edge.from)!.layer;
      const targetLayer = layout.positions.get(edge.to)!.layer;
      expect(layout.rankRoutes[edgeIndex]).toHaveLength(targetLayer - sourceLayer - 1);
      for (const via of layout.rankRoutes[edgeIndex]!)
        for (const node of nodes) {
          const position = layout.positions.get(node.id)!;
          if (position.layer !== via.layer) continue;
          // The renderer traverses this rank vertically at `via.x`; retain
          // ample horizontal room for its stroke and rounded approaches.
          expect(Math.abs(via.x - position.x), `${edgeIndex}/${via.layer}/${node.id}`)
            .toBeGreaterThan(node.width / 2 + 12);
        }
    });
    const lanes = new Map<number, number[]>();
    for (const route of layout.rankRoutes)
      for (const point of route) {
        if (!lanes.has(point.layer)) lanes.set(point.layer, []);
        lanes.get(point.layer)!.push(point.x);
      }
    for (const xs of lanes.values()) {
      xs.sort((a, b) => a - b);
      for (let index = 1; index < xs.length; index += 1)
        expect(xs[index]! - xs[index - 1]!).toBeGreaterThanOrEqual(13.9);
    }
  });

  it("aligns feasible dummy runs and removes collinear bend points", () => {
    const nodes = ["a", "b", "c", "d"].map((id) => ({ id, width: 40 }));
    const edges = [
      { from: "a", to: "b" },
      { from: "b", to: "c" },
      { from: "c", to: "d" },
      { from: "a", to: "d" },
    ];
    const layout = layoutDag({ nodes, edges });
    expect(layout.routes[3]).toHaveLength(2);
    expect(layout.rankRoutes[3]!.map((point) => point.layer)).toEqual([1, 2]);
    expect(layout.routes[3]![0]!.x).toBeCloseTo(layout.routes[3]![1]!.x, 8);
    for (let edge = 0; edge < edges.length; edge += 1) {
      const points = [layout.positions.get(edges[edge]!.from)!, ...layout.routes[edge]!,
        layout.positions.get(edges[edge]!.to)!];
      for (let index = 1; index + 1 < points.length; index += 1) {
        const first = points[index - 1]!;
        const middle = points[index]!;
        const last = points[index + 1]!;
        const fraction = (middle.layer - first.layer) / (last.layer - first.layer);
        const expected = first.x + (last.x - first.x) * fraction;
        expect(Math.abs(middle.x - expected)).toBeGreaterThan(0.35);
      }
    }
  });

  it("keeps a single-assumption proof and its conclusion exactly vertical", () => {
    const nodes = ["a", "p", "u", "v", "c"].map((id) => ({
      id,
      width: id === "p" ? 28 : 52,
    }));
    const edges = [
      { from: "a", to: "p" },
      { from: "p", to: "c" },
      { from: "a", to: "u" },
      { from: "u", to: "v" },
      { from: "v", to: "c" },
    ];
    const layout = layoutDag({ nodes, edges, alignEdgeIndices: [0, 1] });
    const aligned = [
      layout.positions.get("a")!,
      layout.positions.get("p")!,
      ...layout.rankRoutes[1]!,
      layout.positions.get("c")!,
    ];
    for (const point of aligned)
      expect(point.x).toBeCloseTo(aligned[0]!.x, 8);
  });

  it("lays out a skipped-rank 96-vertex DAG within an interactive budget", () => {
    const layerCount = 8;
    const layerWidth = 12;
    const nodes = Array.from({ length: layerCount }, (_, layer) =>
      Array.from({ length: layerWidth }, (__, column) => ({
        id: `n${layer}_${String(column).padStart(2, "0")}`,
        width: 52 + (column % 4) * 7,
      }))).flat();
    const edges: Edge[] = [];
    for (let layer = 0; layer < layerCount - 1; layer += 1)
      for (let column = 0; column < layerWidth; column += 1)
        for (let offset = 0; offset < 3; offset += 1) {
          const skip = 1 + ((column + offset * 3 + layer) %
            Math.min(3, layerCount - layer - 1));
          const target = (column * 7 + offset * 5 + layer * 3) % layerWidth;
          edges.push({
            from: `n${layer}_${String(column).padStart(2, "0")}`,
            to: `n${layer + skip}_${String(target).padStart(2, "0")}`,
          });
        }

    // Warm the VM-backed function once so this measures layout rather than
    // JavaScript compilation. The CI ceiling allows for parallel test-worker
    // contention; the same case benchmarks at roughly 70 ms in isolation.
    layoutDag({ nodes, edges });
    const start = performance.now();
    const layout = layoutDag({ nodes, edges });
    const elapsed = performance.now() - start;
    expect(layout.positions.size).toBe(96);
    expect(layout.maxPairCrossings).toBeLessThanOrEqual(1);
    expect(elapsed).toBeLessThan(500);
  });
});
