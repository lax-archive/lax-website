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

-- Lax323828.BooleanFourier
section
namespace Lax323828
end Lax323828

namespace Lax323828.BooleanFourier
end Lax323828.BooleanFourier
end

-- Lax323828.FiniteProbability
section
namespace Lax323828.FiniteProbability

open scoped Classical

open scoped BigOperators

/-- The proportion of points in the finite sample space satisfying the event `P`. -/
noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax323828.FiniteProbability
end

-- Lax323828.ExponentialBounds
section
namespace Lax323828.ExponentialBounds

open BooleanFourier FiniteProbability

open scoped BigOperators

axiom independent_bounded_upper_tail {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty κ] (F : ι → κ → ℝ)
    (hF : ∀ i z, |F i z| ≤ 1) (hmean : ∀ i, (𝔼 z, F i z) = 0)
    (hN : 0 < Fintype.card ι) (t : ℝ) (ht : 0 ≤ t) :
  probability (fun x : ι → κ ↦ t ≤ ∑ i, F i (x i)) ≤
    Real.exp (-t ^ 2 / (2 * Fintype.card ι))

end Lax323828.ExponentialBounds
end
