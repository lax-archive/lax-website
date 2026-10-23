-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.DecodedStrategies
section
namespace Lax323828.DecodedStrategies
end Lax323828.DecodedStrategies
end

-- Lax323828.LongCode
section
namespace Lax323828
end Lax323828

namespace Lax323828.LongCode
end Lax323828.LongCode
end

-- Lax323828.CNASoundness
section
namespace Lax323828.CNASoundness
end Lax323828.CNASoundness
end

-- Lax323828.ManyTableConsistency
section
namespace Lax323828.ManyTableConsistency
end Lax323828.ManyTableConsistency
end

-- Lax323828.FAFTest
section
namespace Lax323828.FAFTest
end Lax323828.FAFTest
end

-- Lax323828.FAFStrategyExtraction
section
namespace Lax323828.FAFStrategyExtraction
end Lax323828.FAFStrategyExtraction
end

-- Lax323828.ProjectionEncoding
section
namespace Lax323828.ProjectionEncoding.valid
end Lax323828.ProjectionEncoding.valid

namespace Lax323828.ProjectionEncoding

open scoped Classical

open LongCode FiniteProbability

/-- Recover the unique encoded letter if `b` lies in the image of `e`; otherwise return no letter. -/
noncomputable def decode {A B : Type} (e : A ↪ B) (b : B) : Option A :=
  if h : ∃ a, e a = b then some h.choose else none

end Lax323828.ProjectionEncoding
end
