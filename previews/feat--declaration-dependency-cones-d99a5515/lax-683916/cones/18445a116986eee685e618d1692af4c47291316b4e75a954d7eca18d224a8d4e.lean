-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax683916.SymmetricLooplessDigraphs
section
namespace Lax683916.SymmetricLooplessDigraphs

/-- A directed graph whose adjacency relation is symmetric and irreflexive. -/
structure SymmetricLooplessDigraph (V : Type*) where
  /-- The underlying directed graph. -/
  graph : Digraph V
  /-- Every directed edge occurs in both orientations. -/
  symm : Std.Symm graph.Adj
  /-- No vertex is adjacent to itself. -/
  loopless : Std.Irrefl graph.Adj

end Lax683916.SymmetricLooplessDigraphs
end

-- Lax683916.DigraphRepresentation
section
namespace Lax683916.DigraphRepresentation

open Lax683916.SymmetricLooplessDigraphs

universe u

/-- An equivalence that retains exactly the same adjacency relation. -/
structure RepresentationEquiv (V : Type u) where
  /-- The equivalence between the two representation types. -/
  toEquiv : SimpleGraph V ≃ SymmetricLooplessDigraph V
  /-- A directed edge in the image is exactly an edge of the original simple graph. -/
  map_adj : ∀ (G : SimpleGraph V) (u v : V),
    (toEquiv G).graph.Adj u v ↔ G.Adj u v

/-- Simple graphs and symmetric loopless digraphs on the same vertices are equivalent. -/
axiom simpleGraphEquiv (V : Type u) :
  Nonempty (RepresentationEquiv V)

end Lax683916.DigraphRepresentation
end
