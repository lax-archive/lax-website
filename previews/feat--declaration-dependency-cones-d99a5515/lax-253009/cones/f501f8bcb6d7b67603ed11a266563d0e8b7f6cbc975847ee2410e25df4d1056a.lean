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
namespace Lax253009
end Lax253009

namespace Lax253009.BooleanFourier
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
end Lax253009.ExponentialBounds
end

-- Lax253009.RandomFibers
section
namespace Lax253009.RandomFibers

open FiniteProbability

def fiber {ι κ : Type} [Fintype ι] [DecidableEq κ] (f : ι → κ) (z : κ) : Finset ι :=
  Finset.univ.filter fun i ↦ f i = z

axiom small_fiber {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (hN : 0 < Fintype.card ι) (z : κ) :
  probability (fun f : ι → κ ↦ (fiber f z).card <
      (Fintype.card ι : ℝ) / (2 * Fintype.card κ)) ≤
    Real.exp (-(Fintype.card ι : ℝ) / (8 * (Fintype.card κ : ℝ) ^ 2))

end Lax253009.RandomFibers
end
