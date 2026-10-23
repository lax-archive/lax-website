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
namespace Lax323828
end Lax323828

namespace Lax323828.BooleanFourier
end Lax323828.BooleanFourier
end

-- Lax323828.FourierProjection
section
namespace Lax323828.FourierProjection
end Lax323828.FourierProjection
end

-- Lax323828.SmallSupport
section
namespace Lax323828
end Lax323828

namespace Lax323828.SmallSupport
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

def Avoids {ι κ : Type} (D : Finset ι) (f : ι → κ) (y : ι) : Prop :=
  ∀ x ∈ D, f x ≠ f y

end Lax323828.CNAPointSoundness
end
