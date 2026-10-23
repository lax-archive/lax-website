-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

-- Lax253009.HigherMoments
section
namespace Lax253009.HigherMoments
end Lax253009.HigherMoments
end

-- Lax253009.MixedPredicateMoments
section
namespace Lax253009.MixedPredicateMoments

open BooleanFourier BalancedPredicates

open scoped BigOperators

axiom bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (m : ℕ) (S : Fin m → Finset ι) (q : ℝ) (hq : 0 ≤ q) :
  |𝔼 B : Fin m → predicates κ n, 𝔼 f : ι → κ,
      ∏ j, ∏ i ∈ S j, sign ((B j).val (f i))| ≤
    q ^ (Finset.univ.biUnion S).card + (2 : ℝ) ^ m *
      (2 * (Fintype.card κ + 1 : ℝ) * Real.exp (-(Fintype.card κ : ℝ) * q ^ 2 / 2))

end Lax253009.MixedPredicateMoments
end
