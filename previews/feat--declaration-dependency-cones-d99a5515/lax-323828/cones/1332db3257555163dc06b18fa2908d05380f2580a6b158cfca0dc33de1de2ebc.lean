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

-- Lax323828.BalancedCancellation
section
namespace Lax323828.BalancedCancellation
end Lax323828.BalancedCancellation
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

-- Lax323828.LargeCoefficientSoundness
section
namespace Lax323828.LargeCoefficientSoundness

open HighDegreeSoundness

open scoped BigOperators

axiom bound {ι κ : Type} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hN : Fintype.card κ = 2 * n)
    (supports : Finset (Finset ι)) (c : Finset ι → ℝ) (l : ℕ)
    (f : ι → κ) (y : ι) (δ : ℝ) (hδ : 0 < δ) (hl : l < Fintype.card κ)
    (hsupport : ∀ S ∈ supports, y ∈ S ∧ S.card ≤ l ∧ ∀ i ∈ S, i ≠ y → f i ≠ f y)
    (hlarge : ∀ S ∈ supports, δ ≤ |c S|) (henergy : ∑ S ∈ supports, c S ^ 2 ≤ 1) :
  |normalizedSum supports c n f| ≤ (l : ℝ) / ((Fintype.card κ : ℝ) - l) / δ

end Lax323828.LargeCoefficientSoundness
end
