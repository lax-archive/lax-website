-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
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
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.ExponentialBounds
section
namespace Lax253009.ExponentialBounds
end Lax253009.ExponentialBounds
end

-- Lax253009.BalancedPredicates
section
namespace Lax253009.BalancedPredicates

open BooleanFourier FiniteProbability

open scoped BigOperators

def predicates (κ : Type) [Fintype κ] [DecidableEq κ] (n : ℕ) : Finset (Cube κ) :=
  Finset.univ.filter fun B ↦ (Finset.univ.filter fun z ↦ B z = true).card = n

end Lax253009.BalancedPredicates
end

-- Lax253009.ProductMoments
section
namespace Lax253009
end Lax253009

namespace Lax253009.ProductMoments
end Lax253009.ProductMoments
end

-- Lax253009.HighDegreeSoundness
section
namespace Lax253009.HighDegreeSoundness

open BooleanFourier BalancedPredicates FiniteProbability

open scoped BigOperators

noncomputable def normalizedSum {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (supports : Finset (Finset ι)) (c : Finset ι → ℝ) (n : ℕ) (f : ι → κ) : ℝ :=
  ∑ S ∈ supports, c S * (𝔼 B : predicates κ n, ∏ i ∈ S, sign (B.val (f i)))

end Lax253009.HighDegreeSoundness
end
