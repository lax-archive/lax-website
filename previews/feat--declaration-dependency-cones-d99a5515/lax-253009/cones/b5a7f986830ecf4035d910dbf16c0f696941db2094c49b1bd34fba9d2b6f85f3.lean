-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax253009.BooleanFourier
section
namespace Lax253009.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

end Lax253009.BooleanFourier
end

-- Lax253009.FiniteProbability
section
namespace Lax253009.FiniteProbability

open scoped BigOperators

noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax253009.FiniteProbability
end

-- Lax253009.ExponentialBounds
section
namespace Lax253009.ExponentialBounds

open BooleanFourier FiniteProbability

open scoped BigOperators

axiom rademacher_abs_tail {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (v : ℝ) (hv : 0 < v) (hvar : ∑ i, a i ^ 2 ≤ v)
    (t : ℝ) (ht : 0 ≤ t) :
  probability (fun x : Cube ι ↦ t ≤ |∑ i, a i * sign (x i)|) ≤
    2 * Real.exp (-t ^ 2 / (2 * v))

end Lax253009.ExponentialBounds
end
