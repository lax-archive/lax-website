-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.MajorityAmplification
section
namespace Lax323828.MajorityAmplification

open FiniteProbability

def errorMap (p : ℝ) : ℝ := 3 * p ^ 2 - 2 * p ^ 3

end Lax323828.MajorityAmplification
end
