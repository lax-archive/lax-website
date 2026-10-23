-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

-- Lax894236.EulerCharacteristic
section
namespace Lax894236.EulerCharacteristic

open Finset

/-- `d` times the Euler characteristic of a smooth degree-`d` hypersurface of
dimension `n`: the polynomial `(1 - d)^(n+2) - 1 + (n+2) d`. -/
def chiPoly (n : ℕ) (d : ℚ) : ℚ := (1 - d) ^ (n + 2) - 1 + ((n : ℚ) + 2) * d

end Lax894236.EulerCharacteristic
end
