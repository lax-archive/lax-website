import { attr, esc } from "../html.js";

interface ClassBranch {
  concept: string;
  label: string;
  via?: string;
  claim?: string;
  children?: ClassBranch[];
}

/** Editorial overview of lax-68. Each branch is an inclusion, not an assumption
 * of a proof. One route per class keeps this a tree; other inclusions remain in
 * the theorem cards and the separate proof network. */
export const planarClasses: ClassBranch = {
  concept: "Planar", label: "Planar graphs", children: [
    { concept: "Outerplanar", label: "Outerplanar graphs", via: "OuterplanarPlanar", claim: "outerplanar_planar", children: [
      { concept: "MaximalOuterplanar", label: "Maximal outerplanar graphs", via: "MaximalOuterplanarOuterplanar", claim: "maximalOuterplanar_outerplanar", children: [
        { concept: "Triangles", label: "Triangles", via: "TriangleMaximalOuterplanar", claim: "triangle_maximalOuterplanar" },
      ] },
      { concept: "Trees", label: "Finite trees", via: "TreeOuterplanar", claim: "tree_outerplanar", children: [
        { concept: "Stars", label: "Finite stars", via: "StarTree", claim: "star_tree" },
        { concept: "Paths", label: "Paths", via: "PathTree", claim: "path_tree" },
      ] },
    ] },
    { concept: "GridsAndWalls", label: "Grids", via: "GridPlanar", claim: "grid_planar", children: [
      { concept: "Ladders", label: "Ladders", via: "LadderGrid", claim: "ladder_grid" },
    ] },
    { concept: "GridsAndWalls", label: "Walls", via: "WallPlanar", claim: "wall_planar" },
    { concept: "HalinGraphs", label: "Halin graphs", via: "HalinPlanar", claim: "halin_planar", children: [
      { concept: "Wheels", label: "Wheels", via: "WheelHalin", claim: "wheel_halin" },
    ] },
    { concept: "SeriesParallel", label: "Series-parallel graphs", via: "SeriesParallelPlanar", claim: "seriesParallel_planar" },
    { concept: "Triangulations", label: "Triangulations of planar graphs", via: "TriangulationPlanar", claim: "triangulationOf_planar" },
  ],
};

export function planarClassOverview(concepts: ReadonlySet<string>, proven: ReadonlySet<string>): string {
  const link = (id: string, label: string) => `<a href="${attr(`Lax68.${id}.html`)}">${esc(label)}</a>`;
  const all: ClassBranch[] = [];
  const visit = (node: ClassBranch) => { all.push(node); node.children?.forEach(visit); };
  visit(planarClasses);
  const supporting = ["StraightLineDrawings", "KuratowskiPlanarity", "PlanarExcludedMinors", "GraphMinors", "GraphTopologicalMinors"];
  if (![...all.flatMap((n) => [n.concept, ...(n.via ? [n.via] : [])]), ...supporting]
    .every((id) => concepts.has(`Lax68.${id}`))) return "";
  const characterization = (id: string, claim: string, label: string) =>
    `${link(id, label)} (${proven.has(`Lax68.${id}.${claim}`) ? "proved" : "Lean proof open"})`;
  const branch = (node: ClassBranch, parent: string): string => {
    const checked = node.via && proven.has(`Lax68.${node.via}.${node.claim}`);
    return `<li><div class="class-tree-node">${link(node.concept, node.label)}${node.via
      ? `<span class="class-tree-relation">${link(node.via, `⊆ ${parent}`)} <span class="class-tree-status ${checked ? "proved" : "open"}">${checked ? "proved" : "Lean proof open"}</span></span>` : ""}</div>${node.children ? `<ul>${node.children.map((child) => branch(child, node.label)).join("")}</ul>` : ""}</li>`;
  };
  return `<section class="page-section planar-overview" aria-labelledby="class-overview-title">
<h3 class="section-title" id="class-overview-title">Graph-class hierarchy</h3>
<p>Each child belongs to the class above it. This tree shows one route to planarity for every class; each badge reports the child-to-parent theorem only, not the entire route to planarity. Other inclusions and proof dependencies are listed separately below.</p>
<div class="class-tree-root">${link("Planar", "Planar graphs")}
<div class="class-tree-foundations">Defined using ${link("StraightLineDrawings", "straight-line drawings")}.<br>
Characterizations: ${characterization("KuratowskiPlanarity", "planar_iff_kuratowskiFree", "Kuratowski")} (${link("GraphTopologicalMinors", "topological minors")}) and ${characterization("PlanarExcludedMinors", "planar_iff_excludedMinors", "Wagner")} (${link("GraphMinors", "minors")}).</div></div>
<ul class="class-tree" aria-label="Graph classes, from general to special">${planarClasses.children!.map((child) => branch(child, planarClasses.label)).join("")}</ul>
</section>`;
}
