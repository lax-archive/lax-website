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

-- Lax253009.FiniteProbability
section
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.LongCode
section
namespace Lax253009
end Lax253009

namespace Lax253009.LongCode
end Lax253009.LongCode
end

-- Lax253009.CNASoundness
section
namespace Lax253009.CNASoundness
end Lax253009.CNASoundness
end

-- Lax253009.ManyTableConsistency
section
namespace Lax253009.ManyTableConsistency
end Lax253009.ManyTableConsistency
end

-- Lax253009.FAFTest
section
namespace Lax253009.FAFTest
end Lax253009.FAFTest
end

-- Lax253009.LongCodePatterns
section
namespace Lax253009.LongCodePatterns
end Lax253009.LongCodePatterns
end

-- Lax253009.FAFPatterns
section
namespace Lax253009.FAFPatterns
end Lax253009.FAFPatterns
end

-- Lax253009.DecodedStrategies
section
namespace Lax253009.DecodedStrategies
end Lax253009.DecodedStrategies
end

-- Lax253009.FAFStrategyExtraction
section
namespace Lax253009.FAFStrategyExtraction
end Lax253009.FAFStrategyExtraction
end

-- Lax253009.FAFComposition
section
namespace Lax253009.FAFComposition

open LongCode FiniteProbability FAFStrategyExtraction

noncomputable def gameThreshold (l s : ℕ) : ℝ :=
  ((1 / 2 : ℝ) ^ (20 * l * l * s) / 2) * (1 / 2 : ℝ) ^ (20 * l * s) /
    ((2 : ℝ) ^ s + 1)

axiom threshold_positive (l s : ℕ) : 0 < gameThreshold l s

end Lax253009.FAFComposition
end
