import fs from "node:fs";
import { expect, it } from "vitest";
import { layoutGraph } from "../src/graph-layout/index.js";
import type { MeasuredGraph } from "../src/graph-layout/types.js";
import { flattenCommands, segmentIntersection, validateGeometry } from "../src/graph-layout/validate.js";

it("removes the reported Treewidth crossing from the complete measured Lax17 map", () => {
  const fixture = JSON.parse(fs.readFileSync(new URL("./fixtures/graph-layout/lax17-joint-swaps.json", import.meta.url), "utf8")) as {
    graph: MeasuredGraph; baselineCrossings: number;
  };
  const result = layoutGraph(fixture.graph, { inputDigest: "lax17-joint-swaps" });
  expect(result.geometry.nodes).toHaveLength(38);
  expect(result.geometry.edges).toHaveLength(56);
  expect(result.metrics.crossings).toBeLessThan(fixture.baselineCrossings);
  expect(validateGeometry(fixture.graph, result.geometry).diagnostics).toEqual([]);
  const routes = ["HairyPathOfSetsFromTreewidth", "PolynomialGridMinor"].map((target) => {
    const section = result.geometry.edges.find((e) => e.id === `e:Lax17.Treewidth->Lax17.${target}:import:0`)!.sections[0]!;
    return section.commands ? flattenCommands(section.commands) : section.points;
  });
  // These edges have distinct source ports: even a touch away from the box
  // would be ambiguous. Check the final curves, not only the ordering score.
  for (let a = 1; a < routes[0]!.length; a++) for (let b = 1; b < routes[1]!.length; b++)
    expect(segmentIntersection(routes[0]![a - 1]!, routes[0]![a]!, routes[1]![b - 1]!, routes[1]![b]!)).toBeUndefined();
}, 30_000);
