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

end Lax253009.BooleanFourier
end

-- Lax253009.FourierProjection
section
namespace Lax253009.FourierProjection
end Lax253009.FourierProjection
end

-- Lax253009.SmallSupport
section
namespace Lax253009
end Lax253009

namespace Lax253009.SmallSupport
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

def Matches {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (F : Cube ι → ℝ) (n : ℕ) (f : ι → κ) (y : ι) : Prop :=
  ∀ B : predicates κ n, F (fun i ↦ B.val (f i)) = sign (B.val (f y))

end Lax253009.CNAPointSoundness
end
