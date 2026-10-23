-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

noncomputable def character {ι : Type} (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, sign (x i)

noncomputable def average {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ) : ℝ :=
  (∑ x, F x) / (2 : ℝ) ^ Fintype.card ι

noncomputable def coefficient {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ)
    (S : Finset ι) : ℝ :=
  average fun x ↦ F x * character S x

end Lax253009.BooleanFourier
end

-- Lax253009.FourierProjection
section
namespace Lax253009.FourierProjection
end Lax253009.FourierProjection
end

-- Lax253009.SmallSupport
section
namespace Lax253009.SmallSupport

noncomputable def largeSets {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter fun a ↦ a.card ≤ l ∧ (l : ℝ) * δ ≤ c a ^ 2

noncomputable def decodingSet {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset ι :=
  (largeSets c l δ).biUnion id

end Lax253009.SmallSupport
end

-- Lax253009.FourierDecoding
section
namespace Lax253009.FourierDecoding
end Lax253009.FourierDecoding
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
end Lax253009.HighDegreeSoundness
end

-- Lax253009.BalancedCancellation
section
namespace Lax253009.BalancedCancellation
end Lax253009.BalancedCancellation
end

-- Lax253009.LargeCoefficientSoundness
section
namespace Lax253009.LargeCoefficientSoundness
end Lax253009.LargeCoefficientSoundness
end

-- Lax253009.HigherMoments
section
namespace Lax253009.HigherMoments
end Lax253009.HigherMoments
end

-- Lax253009.MixedPredicateMoments
section
namespace Lax253009.MixedPredicateMoments
end Lax253009.MixedPredicateMoments
end

-- Lax253009.Hypercontractivity
section
namespace Lax253009.Hypercontractivity
end Lax253009.Hypercontractivity
end

-- Lax253009.DoubleCoverBounds
section
namespace Lax253009.DoubleCoverBounds
end Lax253009.DoubleCoverBounds
end

-- Lax253009.SmallUnionDoubleCovers
section
namespace Lax253009.SmallUnionDoubleCovers
end Lax253009.SmallUnionDoubleCovers
end

-- Lax253009.SmallCoefficientSoundness
section
namespace Lax253009.SmallCoefficientSoundness
end Lax253009.SmallCoefficientSoundness
end

-- Lax253009.CNAPointSoundness
section
namespace Lax253009.CNAPointSoundness

open BooleanFourier BalancedPredicates FiniteProbability

noncomputable def decoding {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l : ℕ) (τ : ℝ) : Finset ι :=
  SmallSupport.decodingSet (coefficient F) l (τ ^ 2 / l)

axiom decoding_card {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (hF : ∀ x, |F x| ≤ 1)
    (l : ℕ) (hl : 0 < l) (τ : ℝ) (hτ : 0 < τ) :
  ((decoding F l τ).card : ℝ) ≤ (l : ℝ) / τ ^ 2

end Lax253009.CNAPointSoundness
end
