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
end Lax323828.ExponentialBounds
end

-- Lax323828.RandomFibers
section
namespace Lax323828.RandomFibers

open FiniteProbability

def fiber {ι κ : Type} [Fintype ι] [DecidableEq κ] (f : ι → κ) (z : κ) : Finset ι :=
  Finset.univ.filter fun i ↦ f i = z

axiom any_small_fiber {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (hN : 0 < Fintype.card ι) :
  probability (fun f : ι → κ ↦ ∃ z, (fiber f z).card <
      (Fintype.card ι : ℝ) / (2 * Fintype.card κ)) ≤
    (Fintype.card κ : ℝ) *
      Real.exp (-(Fintype.card ι : ℝ) / (8 * (Fintype.card κ : ℝ) ^ 2))

end Lax323828.RandomFibers
end
