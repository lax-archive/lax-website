import { compareIds, type SiteModel } from "./model.js";

/** Placement relative to a figure's roots: the always-visible core (the roots
 * themselves), or a direction away from them — "up" for the whole ancestry,
 * "down" for everything that builds on a root. */
export type GraphDir = "core" | "up" | "down";

export interface ConceptGraphNode {
  id: string;
  href: string;
  /** the concept's human title, for the hover tooltip */
  title: string;
  /** home submission id */
  owner: string;
  /** proven claim, open claim, or a definition-concept with no claim status */
  status: "proven" | "open" | "none";
  ext: boolean;
  /** placement relative to the page's roots, behind the figure's toggles */
  dir: GraphDir;
}

export interface ConceptGraphEdge {
  from: string;
  to: string;
}

export interface ConceptGraphData {
  nodes: ConceptGraphNode[];
  edges: ConceptGraphEdge[];
}

export interface SubmissionGraphNode {
  id: string;
  href: string;
  /** the submission's title, for the hover tooltip */
  title: string;
  state: string;
  concepts: number;
  proofs: number;
  dir: GraphDir;
  ext: boolean;
}

export interface SubmissionGraphData {
  nodes: SubmissionGraphNode[];
  edges: ConceptGraphEdge[];
}

/** Build the semantic import graph around one or more roots: the roots form
 * the always-shown core, the whole upstream closure and the whole downstream
 * closure are tagged for the figure's two all-or-nothing toggles.
 * Descendants' unrelated imports stay out of view — the graph never grows
 * beyond the roots' own ancestry and posterity. */
export function conceptGraph(model: SiteModel, rootIds: Iterable<string>): ConceptGraphData {
  const roots = new Set([...rootIds].filter((id) => model.conceptHome.has(id)));
  const dirOf = new Map<string, GraphDir>();
  for (const id of roots) dirOf.set(id, "core");
  for (const id of roots)
    for (const ancestor of model.upstreamClosure(id))
      if (!dirOf.has(ancestor.concept.id)) dirOf.set(ancestor.concept.id, "up");
  for (const id of roots)
    for (const descendant of model.downstreamClosure(id))
      if (!dirOf.has(descendant.concept.id)) dirOf.set(descendant.concept.id, "down");

  const ids = new Set(dirOf.keys());
  const nodes = [...ids].sort().map((id) => {
    const home = model.conceptHome.get(id)!;
    const statement = home.concept.statements[0];
    const status = !statement
      ? ("none" as const)
      : model.network.proven.has(statement.id)
        ? ("proven" as const)
        : ("open" as const);
    return {
      id,
      href: `../${home.output.id}/${id}.html`,
      title: home.concept.title,
      owner: home.output.id,
      status,
      ext: !roots.has(id),
      dir: dirOf.get(id)!,
    };
  });
  const edges = [...ids]
    .sort()
    .flatMap((id) =>
      model.conceptHome.get(id)!.concept.imports
        .filter((from) => ids.has(from))
        .map((from) => ({ from, to: id })),
    );
  return { nodes, edges };
}

/** The concept map one level up: the page's own submission, everything it
 * transitively builds on, and everything that transitively builds on it.
 * Both directions run over the whole archive, and both are always shown —
 * submissions are few enough that the figure needs no toggles. Edges between
 * two neighbours are kept as well, so a dependency that bypasses the root
 * stays visible instead of being redrawn through it. */
export function submissionGraph(model: SiteModel, rootId: string): SubmissionGraphData {
  const dirOf = new Map<string, GraphDir>();
  if (model.submissionUses.has(rootId)) dirOf.set(rootId, "core");
  for (const id of model.submissionUpstream(rootId)) dirOf.set(id, "up");
  for (const id of model.submissionDownstream(rootId)) if (!dirOf.has(id)) dirOf.set(id, "down");

  const ids = [...dirOf.keys()].sort(compareIds);
  const nodes = ids.map((id) => {
    const submission = model.submissionById.get(id)!;
    const output = submission.output!;
    return {
      id,
      href: `../${id}/index.html`,
      title: output.manifest.title,
      state: submission.record.state,
      concepts: output.concepts.length,
      proofs: output.proofs.length,
      dir: dirOf.get(id)!,
      ext: id !== rootId,
    };
  });
  const edges = ids.flatMap((id) =>
    [...model.submissionUses.get(id)!]
      .filter((from) => dirOf.has(from))
      .sort(compareIds)
      .map((from) => ({ from, to: id })));
  return { nodes, edges };
}

/** CSP-safe inert graph payload consumed by assets/dag.js. */
export function graphDataScript(data: unknown): string {
  return `<script type="application/json" id="graph-data">${JSON.stringify(data).replace(/</g, "\\u003c")}</script>`;
}
