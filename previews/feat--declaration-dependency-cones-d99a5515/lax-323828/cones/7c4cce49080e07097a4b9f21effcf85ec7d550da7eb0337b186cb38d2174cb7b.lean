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

-- Lax323828.BooleanFourier
section
namespace Lax323828.BooleanFourier

abbrev Cube (ι : Type) := ι → Bool

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def character {ι : Type} (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, sign (x i)

noncomputable def average {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ) : ℝ :=
  (∑ x, F x) / (2 : ℝ) ^ Fintype.card ι

noncomputable def coefficient {ι : Type} [Fintype ι] [DecidableEq ι] (F : Cube ι → ℝ)
    (S : Finset ι) : ℝ :=
  average fun x ↦ F x * character S x

end Lax323828.BooleanFourier
end

-- Lax323828.FourierProjection
section
namespace Lax323828.FourierProjection
end Lax323828.FourierProjection
end

-- Lax323828.SmallSupport
section
namespace Lax323828.SmallSupport

open scoped Classical

/-- The coordinate sets of size at most `l` whose squared coefficient is at least `l * δ`. -/
noncomputable def largeSets {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset (Finset ι) :=
  Finset.univ.filter fun a ↦ a.card ≤ l ∧ (l : ℝ) * δ ≤ c a ^ 2

/-- The union of the coordinate sets selected by `largeSets`. -/
noncomputable def decodingSet {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset ι :=
  (largeSets c l δ).biUnion id

end Lax323828.SmallSupport
end

-- Lax323828.FourierDecoding
section
namespace Lax323828.FourierDecoding
end Lax323828.FourierDecoding
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
end Lax323828.HighDegreeSoundness
end

-- Lax323828.BalancedCancellation
section
namespace Lax323828.BalancedCancellation
end Lax323828.BalancedCancellation
end

-- Lax323828.LargeCoefficientSoundness
section
namespace Lax323828.LargeCoefficientSoundness
end Lax323828.LargeCoefficientSoundness
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
end Lax323828.SmallCoefficientSoundness
end

-- Lax323828.CNAPointSoundness
section
namespace Lax323828.CNAPointSoundness

open BooleanFourier BalancedPredicates FiniteProbability

noncomputable def decoding {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Cube ι → ℝ) (l : ℕ) (τ : ℝ) : Finset ι :=
  SmallSupport.decodingSet (coefficient F) l (τ ^ 2 / l)

end Lax323828.CNAPointSoundness
end
