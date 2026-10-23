-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.Hypergraph.Basic

-- Lax683916.SpanningTwoUniformHypergraphs
section
namespace Lax683916.SpanningTwoUniformHypergraphs

/-- A hypergraph with full vertex set and two-element edges. -/
structure SpanningTwoUniformHypergraph (V : Type*) where
  /-- The underlying hypergraph. -/
  hypergraph : Hypergraph V
  /-- Every element of the ambient type is a vertex. -/
  spanning : hypergraph.vertexSet = Set.univ
  /-- Every hyperedge contains exactly two vertices. -/
  twoUniform : ∀ e ∈ hypergraph.edgeSet, Set.ncard e = 2

end Lax683916.SpanningTwoUniformHypergraphs
end
