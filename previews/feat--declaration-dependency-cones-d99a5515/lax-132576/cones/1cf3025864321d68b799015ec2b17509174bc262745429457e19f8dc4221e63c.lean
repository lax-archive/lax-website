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

/-- A partial function has bounded variation if for all `w₁, w₂` the left distances
`‖f (w w₁), f (w w₂)‖` are bounded, over the `w` for which both are defined. -/
def BoundedVariation {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∀ w₁ w₂ : List A, ∃ K : ℕ, ∀ (w : List A) (v₁ v₂ : List B),
    f (w ++ w₁) = some v₁ → f (w ++ w₂) = some v₂ → leftDist v₁ v₂ ≤ K

end Lax132576.LeftDistance
end
