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
namespace Lax323828.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

end Lax323828.BooleanFourier
end

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.ExponentialBounds
section
namespace Lax323828.ExponentialBounds

open BooleanFourier FiniteProbability

open scoped BigOperators

axiom rademacher_mgf {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (u : ℝ) :
  (𝔼 x : Cube ι, Real.exp (u * ∑ i, a i * sign (x i))) ≤
    Real.exp (u ^ 2 / 2 * ∑ i, a i ^ 2)

end Lax323828.ExponentialBounds
end
