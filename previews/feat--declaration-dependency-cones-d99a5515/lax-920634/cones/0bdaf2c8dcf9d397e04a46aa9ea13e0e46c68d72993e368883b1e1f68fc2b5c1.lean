-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card

-- Lax920634.EdgeExpansion
section
namespace Lax920634.EdgeExpansion

/-- Boundary edges oriented from the set to its complement, each counted once. -/
def edgeBoundary {V : Type} (G : SimpleGraph V) (S : Set V) : Set (V × V) :=
  {e | e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2}

/-- Every vertex set of size at most half the graph has at least `h` times
its size in boundary edges. -/
def HasEdgeExpansionAtLeast {V : Type} [Fintype V]
    (G : SimpleGraph V) (h : ℚ) : Prop :=
  ∀ S : Set V, 2 * S.ncard ≤ Fintype.card V →
    h * (S.ncard : ℚ) ≤ ((edgeBoundary G S).ncard : ℚ)

end Lax920634.EdgeExpansion
end
