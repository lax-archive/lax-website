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

end Lax253009.BooleanFourier
end

-- Lax253009.Hypercontractivity
section
namespace Lax253009.Hypercontractivity

open BooleanFourier

open scoped BigOperators

axiom fourth_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (l : ℕ) (hdegree : ∀ S, l < S.card → c S = 0) :
  (𝔼 x : Cube ι, (∑ S, c S * character S x) ^ 4) ≤
    ((3 : ℝ) ^ l * ∑ S, c S ^ 2) ^ 2

end Lax253009.Hypercontractivity
end
