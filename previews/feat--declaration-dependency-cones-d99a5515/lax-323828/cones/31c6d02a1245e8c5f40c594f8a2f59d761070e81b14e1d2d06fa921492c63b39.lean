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
end Lax323828.ExponentialBounds
end

-- Lax323828.BalancedPredicates
section
namespace Lax323828.BalancedPredicates

open BooleanFourier FiniteProbability

open scoped BigOperators

def predicates (κ : Type) [Fintype κ] [DecidableEq κ] (n : ℕ) : Finset (Cube κ) :=
  Finset.univ.filter fun B ↦ (Finset.univ.filter fun z ↦ B z = true).card = n

end Lax323828.BalancedPredicates
end

-- Lax323828.ProductMoments
section
namespace Lax323828
end Lax323828

namespace Lax323828.ProductMoments
end Lax323828.ProductMoments
end

-- Lax323828.HighDegreeSoundness
section
namespace Lax323828.HighDegreeSoundness

open BooleanFourier BalancedPredicates FiniteProbability

open scoped BigOperators

noncomputable def normalizedSum {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (supports : Finset (Finset ι)) (c : Finset ι → ℝ) (n : ℕ) (f : ι → κ) : ℝ :=
  ∑ S ∈ supports, c S * (𝔼 B : predicates κ n, ∏ i ∈ S, sign (B.val (f i)))

end Lax323828.HighDegreeSoundness
end

-- Lax323828.HigherMoments
section
namespace Lax323828.HigherMoments
end Lax323828.HigherMoments
end

-- Lax323828.MixedPredicateMoments
section
namespace Lax323828.MixedPredicateMoments
end Lax323828.MixedPredicateMoments
end

-- Lax323828.Hypercontractivity
section
namespace Lax323828.Hypercontractivity
end Lax323828.Hypercontractivity
end

-- Lax323828.DoubleCoverBounds
section
namespace Lax323828.DoubleCoverBounds
end Lax323828.DoubleCoverBounds
end

-- Lax323828.SmallUnionDoubleCovers
section
namespace Lax323828.SmallUnionDoubleCovers
end Lax323828.SmallUnionDoubleCovers
end

-- Lax323828.SmallCoefficientSoundness
section
namespace Lax323828.SmallCoefficientSoundness

open HighDegreeSoundness FiniteProbability

open scoped BigOperators

noncomputable def boundValue (l m r N : ℕ) (δ q : ℝ) : ℝ :=
  (∑ t ∈ Finset.range r, (2 : ℝ) ^ m * ((2 : ℝ) ^ t * δ) ^ (m - 2 * t) *
    (1 + (3 : ℝ) ^ (l * (4 * t + 1) * 2 ^ (2 * t)))) +
  (1 + (3 : ℝ) ^ (l * (2 * m + 1) * 2 ^ m)) *
    (q ^ r + (2 : ℝ) ^ m * (2 * (N + 1 : ℝ) * Real.exp (-(N : ℝ) * q ^ 2 / 2)))

axiom moment_bound {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (n : ℕ) (hn : 0 < n) (hN : Fintype.card κ = 2 * n)
    (c : Finset ι → ℝ) (l m r : ℕ) (δ q : ℝ)
    (hsmall : ∀ S, |c S| ≤ δ) (hδ : 0 ≤ δ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hdegree : ∀ S, l < S.card → c S = 0) (henergy : ∑ S, c S ^ 2 ≤ 1)
    (hr : 2 * r ≤ m) :
  (𝔼 f : ι → κ, normalizedSum Finset.univ c n f ^ m) ≤
    boundValue l m r (Fintype.card κ) δ q

end Lax323828.SmallCoefficientSoundness
end
