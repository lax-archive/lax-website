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
namespace Lax253009
end Lax253009

namespace Lax253009.BooleanFourier
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

open HighDegreeSoundness FiniteProbability

open scoped BigOperators

noncomputable def boundValue (l m r N : ℕ) (δ q : ℝ) : ℝ :=
  (∑ t ∈ Finset.range r, (2 : ℝ) ^ m * ((2 : ℝ) ^ t * δ) ^ (m - 2 * t) *
    (1 + (3 : ℝ) ^ (l * (4 * t + 1) * 2 ^ (2 * t)))) +
  (1 + (3 : ℝ) ^ (l * (2 * m + 1) * 2 ^ m)) *
    (q ^ r + (2 : ℝ) ^ m * (2 * (N + 1 : ℝ) * Real.exp (-(N : ℝ) * q ^ 2 / 2)))

end Lax253009.SmallCoefficientSoundness
end

-- Lax253009.CNAPointSoundness
section
namespace Lax253009.CNAPointSoundness

open BooleanFourier BalancedPredicates FiniteProbability

noncomputable def pointBound (l m r N : ℕ) (τ q : ℝ) : ℝ :=
  9 * (q ^ l + 2 * (N + 1 : ℝ) * Real.exp (-(N : ℝ) * q ^ 2 / 2)) +
    (3 : ℝ) ^ m * SmallCoefficientSoundness.boundValue l m r N τ q

end Lax253009.CNAPointSoundness
end
