-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

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

-- Lax683916.HypergraphRepresentation
section
namespace Lax683916.HypergraphRepresentation

open Lax683916.SpanningTwoUniformHypergraphs

universe u

/-- An equivalence that sends graph edges to two-element hyperedges. -/
structure RepresentationEquiv (V : Type u) where
  /-- The equivalence between the two representation types. -/
  toEquiv : SimpleGraph V ≃ SpanningTwoUniformHypergraph V
  /-- A pair is a hyperedge in the image exactly when its two elements are adjacent. -/
  map_pair : ∀ (G : SimpleGraph V) (u v : V),
    {u, v} ∈ (toEquiv G).hypergraph.edgeSet ↔ G.Adj u v

/-- Simple graphs and spanning 2-uniform hypergraphs on the same vertices are equivalent. -/
axiom simpleGraphEquiv (V : Type u) :
  Nonempty (RepresentationEquiv V)

end Lax683916.HypergraphRepresentation
end
