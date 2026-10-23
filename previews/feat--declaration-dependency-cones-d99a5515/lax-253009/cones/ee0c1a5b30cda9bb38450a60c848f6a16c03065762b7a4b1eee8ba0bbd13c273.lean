-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.MajorityAmplification
section
namespace Lax253009.MajorityAmplification

open FiniteProbability

def errorMap (p : ℝ) : ℝ := 3 * p ^ 2 - 2 * p ^ 3

axiom three_rounds (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1 / 3) :
    errorMap (errorMap (errorMap p)) ≤ 1 / 12

end Lax253009.MajorityAmplification
end
