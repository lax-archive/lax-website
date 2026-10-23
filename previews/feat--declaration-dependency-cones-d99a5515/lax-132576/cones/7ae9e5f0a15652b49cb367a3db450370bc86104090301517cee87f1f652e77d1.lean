-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic

-- Lax132576.LeftDistance
section
namespace Lax132576.LeftDistance

/-- The left distance `‖w₁, w₂‖`: the least `k` such that `w₁ = v v₁` and
`w₂ = v v₂` with `|v₁|, |v₂| ≤ k`. -/
noncomputable def leftDist {B : Type} (w₁ w₂ : List B) : ℕ :=
  sInf {k : ℕ | ∃ v v₁ v₂ : List B,
    w₁ = v ++ v₁ ∧ w₂ = v ++ v₂ ∧ v₁.length ≤ k ∧ v₂.length ≤ k}

/-- The relation `w₁ ∼ w₂` of Theorem B.4.13: the left distances
`‖f (w w₁), f (w w₂)‖` are bounded uniformly in `w`. -/
def BoundedVarRel {A B : Type} (f : List A → List B) (w₁ w₂ : List A) : Prop :=
  ∃ K : ℕ, ∀ w : List A, leftDist (f (w ++ w₁)) (f (w ++ w₂)) ≤ K

end Lax132576.LeftDistance
end
