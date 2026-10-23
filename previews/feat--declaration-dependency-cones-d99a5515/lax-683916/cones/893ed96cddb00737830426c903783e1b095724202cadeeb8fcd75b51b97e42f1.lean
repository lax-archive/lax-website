-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.Digraph.Basic

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
