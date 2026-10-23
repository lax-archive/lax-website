-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax253009.BooleanFourier
section
namespace Lax253009.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def character {ι : Type} (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, sign (x i)

noncomputable def average {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ) : ℝ :=
  (∑ x, F x) / (2 : ℝ) ^ Fintype.card ι

noncomputable def coefficient {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ)
    (S : Finset ι) : ℝ :=
  average fun x ↦ F x * character S x

end Lax253009.BooleanFourier
end

-- Lax253009.Hypercontractivity
section
namespace Lax253009.Hypercontractivity

open BooleanFourier

open scoped BigOperators

axiom dyadic_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l k : ℕ) (hdegree : ∀ S, l < S.card → coefficient F S = 0) :
  (𝔼 x, F x ^ (2 ^ (k + 1))) ≤
    (3 : ℝ) ^ (l * k * 2 ^ k) * (𝔼 x, F x ^ 2) ^ (2 ^ k)

end Lax253009.Hypercontractivity
end
