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

def vote (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

end Lax253009.MajorityAmplification
end
