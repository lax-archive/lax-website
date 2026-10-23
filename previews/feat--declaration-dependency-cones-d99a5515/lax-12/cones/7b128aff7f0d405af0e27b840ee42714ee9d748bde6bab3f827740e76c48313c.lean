-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

-- Lax12.GraphClasses
section
namespace Lax12.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax12.GraphClasses
end

-- Lax12.NeighborhoodComplexity
section
namespace Lax12.NeighborhoodComplexity

open Lax12.GraphClasses

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

end Lax12.NeighborhoodComplexity
end
