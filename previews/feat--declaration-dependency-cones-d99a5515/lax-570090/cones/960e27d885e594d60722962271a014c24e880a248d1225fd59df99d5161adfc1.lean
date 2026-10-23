-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Real.Basic

-- Lax570090.VertexRemovalStability
section
namespace Lax570090.VertexRemovalStability

open SimpleGraph

/-- The number of (unordered) edges of a finite simple graph. -/
noncomputable def edgeCount {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

axiom exists_fiveColorable_delete
    {V : Type*} [Fintype V] (G : SimpleGraph V) (eps : ℝ)
    (hepsPos : 0 < eps) (hepsSmall : eps < 1 / 3750)
    (hcard : 20 ≤ Fintype.card V) (hK6 : G.CliqueFree 6)
    (hedges :
      (SimpleGraph.extremalNumber (Fintype.card V) (⊤ : SimpleGraph (Fin 6)) : ℝ) -
          eps * (Fintype.card V : ℝ) ^ 2 < edgeCount G) :
    ∃ Z : Set V,
      (Nat.card Z : ℝ) < 3500 * eps * Fintype.card V ∧
        (G.induce Zᶜ).Colorable 5

end Lax570090.VertexRemovalStability
end
