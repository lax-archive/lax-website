-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

-- Lax199508.GraphClasses
section
namespace Lax199508.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax199508.GraphClasses
end

-- Lax199508.NeighborhoodComplexity
section
namespace Lax199508.NeighborhoodComplexity

open Lax199508.GraphClasses

/-- The number of distinct neighborhood traces `N(v) ∩ A` that the
vertices of `G` leave on the vertex set `A`. -/
noncomputable def traceCount {V : Type*} (G : SimpleGraph V)
    (A : Set V) : ℕ :=
  {S : Set V | ∃ v : V, S = G.neighborSet v ∩ A}.ncard

/-- Every graph in the class leaves at most `c · |A|^(1+ε)` neighborhood
traces on every nonempty vertex subset `A`, where `c` depends only on
`ε > 0`: neighborhood complexity `|A|^(1+o(1))`. -/
def HasAlmostLinearNC (C : GraphClass) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Set (Fin n), A.Nonempty →
        (traceCount G A : ℝ) ≤ c * (A.ncard : ℝ) ^ (1 + ε)

end Lax199508.NeighborhoodComplexity
end
