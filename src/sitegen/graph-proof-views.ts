import { compareText, deepFreeze } from "../graph-layout/normalize.js";
import { projectGraph, type DisplayGraph, type ProofGraphData, type StatementGraphInput } from "./graph-project.js";

/** The overview is a quotient by concept file. It summarizes all available
 * proofs, including alternatives; only the local views express individual
 * proof obligations and their conjunctions. */
export function proofGraphViews(data: ProofGraphData): { state: string; display: DisplayGraph; status: string }[] {
  const concepts = new Map<string, StatementGraphInput[]>();
  const homes = new Map<string, string>();
  for (const statement of data.statements) {
    const id = statement.concept ?? statement.id;
    const members = concepts.get(id) ?? [];
    members.push(statement); concepts.set(id, members);
    homes.set(statement.id, id); homes.set(id, id);
  }
  const ids = [...concepts.keys()].sort(compareText);
  const conceptNode = (id: string): StatementGraphInput => {
    const members = concepts.get(id)!, sample = members[0]!;
    const statements = members.filter((member) => member.endpointKind !== "concept");
    return { ...sample, id, concept: id, endpointKind: "concept", index: undefined, count: 1,
      href: sample.href?.split("#")[0], ext: members.every((member) => member.ext),
      proven: statements.length ? statements.every((member) => member.proven) : sample.proven,
      status: statements.length ? statements.every((member) => member.proven) ? "proven" : "open" : sample.status };
  };
  const grouped = new Map(ids.map((id) => [id, data.proofs.filter((proof) => homes.get(proof.conclusion) === id)]));
  const summaries = ids.filter((id) => grouped.get(id)!.length).map((id) => {
    const proofs = grouped.get(id)!;
    const assumptions = [...new Set(proofs.flatMap((proof) => proof.assumptions.map((assumption) => homes.get(assumption)!)))]
      .filter((assumption) => assumption !== id).sort(compareText);
    return { id: `concept-proof:${id}`, conclusion: id, assumptions,
      href: conceptNode(id).href, ext: proofs.every((proof) => proof.ext),
      description: `${proofs.length} proof${proofs.length === 1 ? "" : "s"} of ${conceptNode(id).label ?? id}` };
  });
  const overview = projectGraph("proofs", { statements: ids.map(conceptNode), proofs: summaries,
    nodeScale: Math.min(4, 1.4 * (data.nodeScale ?? 1)) });
  const display: DisplayGraph = deepFreeze({ ...overview,
    nodes: overview.nodes.map((node) => {
      const concept = node.kind === "proof" ? node.semanticId.slice("concept-proof:".length) : node.semanticId;
      return { ...node, detailView: `statements:${concept}`, detailConcept: concept };
    }),
  });
  const views = [{ state: "default", display, status: `${ids.length} concept files; connections summarize their proofs` }];
  for (const id of ids) {
    const proofs = grouped.get(id)!;
    const members = concepts.get(id)!;
    const statements = members.filter((statement) => statement.endpointKind !== "concept");
    // Only the overview groups a file into one box. In a local view each
    // numbered statement is an independent vertex, so sibling dependencies
    // are ordinary directed paths instead of artificial display cycles.
    const localStatements = statements.length > 1 ? statements.map((statement) => ({ ...statement,
      concept: undefined, index: undefined, count: 1, label: String(statement.index),
      title: `Statement ${statement.index}: ${statement.id}`, tooltipHtml: undefined,
    })) : [...statements];
    if (!localStatements.some((statement) => statement.id === id) &&
        (!statements.length || proofs.some((proof) => proof.conclusion === id || proof.assumptions.includes(id))))
      localStatements.push(conceptNode(id));
    const premises = [...new Set(proofs.flatMap((proof) => proof.assumptions.map((assumption) => homes.get(assumption)!)))]
      .filter((premise) => premise !== id).sort(compareText);
    const local = projectGraph("proofs", {
      statements: [...localStatements, ...premises.map(conceptNode)],
      proofs: proofs.map((proof) => ({ ...proof,
        assumptions: [...new Set(proof.assumptions.map((assumption) => homes.get(assumption) === id ? assumption : homes.get(assumption)!))],
      })),
    });
    views.push({ state: `statements:${id}`, display: { ...local, proofDetail: id },
      status: `${statements.length} statement${statements.length === 1 ? "" : "s"}; ${proofs.length} proof${proofs.length === 1 ? "" : "s"}` });
  }
  return views;
}
