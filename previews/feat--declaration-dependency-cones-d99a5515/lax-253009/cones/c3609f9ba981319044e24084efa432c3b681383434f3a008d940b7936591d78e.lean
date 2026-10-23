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

open BooleanFourier FiniteProbability

open scoped BigOperators

axiom exponential_markov {α : Type} [Fintype α] [Nonempty α]
    (X : α → ℝ) (t u : ℝ) (hu : 0 ≤ u) :
  probability (fun x ↦ t ≤ X x) ≤ Real.exp (-u * t) * (𝔼 x, Real.exp (u * X x))

end Lax253009.ExponentialBounds
end
