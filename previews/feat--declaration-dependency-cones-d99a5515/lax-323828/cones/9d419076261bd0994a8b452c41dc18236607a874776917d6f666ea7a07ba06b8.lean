-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
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

-- Lax323828.LongCodePatterns
section
namespace Lax323828.LongCodePatterns
end Lax323828.LongCodePatterns
end

-- Lax323828.FAFPatterns
section
namespace Lax323828.FAFPatterns
end Lax323828.FAFPatterns
end

-- Lax323828.DecodedStrategies
section
namespace Lax323828.DecodedStrategies
end Lax323828.DecodedStrategies
end

-- Lax323828.FAFStrategyExtraction
section
namespace Lax323828.FAFStrategyExtraction
end Lax323828.FAFStrategyExtraction
end

-- Lax323828.FAFComposition
section
namespace Lax323828.FAFComposition

open LongCode FiniteProbability FAFStrategyExtraction

noncomputable def gameThreshold (l s : ℕ) : ℝ :=
  ((1 / 2 : ℝ) ^ (20 * l * l * s) / 2) * (1 / 2 : ℝ) ^ (20 * l * s) /
    ((2 : ℝ) ^ s + 1)

end Lax323828.FAFComposition
end
