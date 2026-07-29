import type { BuildOutput } from "../types.js";

export interface ProofNetwork {
  /** every statement id in the corpus */
  statements: Set<string>;
  /** proven statement ids (least fixed point) */
  proven: Set<string>;
  /** hyperedges: proof id, assumption set, conclusion */
  edges: { id: string; assumptions: string[]; conclusion: string }[];
}

/**
 * The proof network: the directed hypergraph over all statements with a
 * hyperedge (A -> c) for every proof. A statement is proven if it is the
 * conclusion of some proof all of whose assumptions are recursively proven —
 * a least fixed point, so statements in a dependency cycle do not prove each
 * other.
 */
export function computeNetwork(outputs: BuildOutput[]): ProofNetwork {
  const statements = new Set<string>();
  const edges: ProofNetwork["edges"] = [];
  for (const out of outputs) {
    for (const concept of out.concepts)
      for (const s of concept.statements) statements.add(s.id);
    for (const proof of out.proofs)
      edges.push({ id: proof.id, assumptions: proof.assumptions, conclusion: proof.conclusion });
  }

  const proven = new Set<string>();
  let changed = true;
  while (changed) {
    changed = false;
    for (const edge of edges) {
      if (proven.has(edge.conclusion)) continue;
      if (!statements.has(edge.conclusion)) continue;
      if (edge.assumptions.every((a) => proven.has(a))) {
        proven.add(edge.conclusion);
        changed = true;
      }
    }
  }
  return { statements, proven, edges };
}
