-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
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

-- Lax253009.LongCode
section
namespace Lax253009.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

end Lax253009.LongCode
end

-- Lax253009.SideConditionAveraging
section
namespace Lax253009.SideConditionAveraging

open LongCode BooleanFourier FourierProjection

def satisfying {w : ℕ} (h : Coordinate w) : Finset (Word w) :=
  Finset.univ.filter fun x ↦ h x = true

end Lax253009.SideConditionAveraging
end
