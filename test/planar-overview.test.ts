import { describe, expect, it } from "vitest";
import { planarClasses, planarClassOverview } from "../src/sitegen/pages/planar-overview.js";

function conceptIds() {
  const ids = new Set(["StraightLineDrawings", "KuratowskiPlanarity", "PlanarExcludedMinors", "GraphMinors", "GraphTopologicalMinors"].map((s) => `Lax68.${s}`));
  const walk = (n: typeof planarClasses) => {
    ids.add(`Lax68.${n.concept}`);
    if (n.via) ids.add(`Lax68.${n.via}`);
    n.children?.forEach(walk);
  };
  walk(planarClasses);
  return ids;
}

describe("planar class overview", () => {
  it("connects every class to Planar with a theorem for each parent relation", () => {
    const labels = new Set<string>();
    const walk = (n: typeof planarClasses, root = false) => {
      expect(labels.has(n.label)).toBe(false);
      labels.add(n.label);
      if (!root) { expect(n.via).toBeTruthy(); expect(n.claim).toBeTruthy(); }
      n.children?.forEach((child) => walk(child));
    };
    walk(planarClasses, true);
    expect(labels.size).toBe(14);
    const html = planarClassOverview(conceptIds(), new Set());
    expect(html).toContain('aria-label="Graph classes, from general to special"');
    expect(html.match(/Lean proof open/g)).toHaveLength(15);
    expect(html).toContain('Lax68.TriangulationPlanar.html');
  });

  it("uses proof closure status without treating an open result as proved", () => {
    const html = planarClassOverview(conceptIds(), new Set(["Lax68.StarTree.star_tree"]));
    expect(html.match(/class-tree-status proved/g)).toHaveLength(1);
    expect(html.match(/Lean proof open/g)).toHaveLength(14);
  });

  it("omits the editorial map when its required concepts are absent", () => {
    const ids = conceptIds(); ids.delete("Lax68.StarTree");
    expect(planarClassOverview(ids, new Set())).toBe("");
  });
});
