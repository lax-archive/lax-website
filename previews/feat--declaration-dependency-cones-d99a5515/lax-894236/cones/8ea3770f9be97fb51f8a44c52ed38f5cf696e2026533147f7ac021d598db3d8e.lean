-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs

-- Lax894236.LinearSubspaceClass
section
namespace Lax894236.LinearSubspaceClass

/-- For `d ≥ 2` there is no rational `c` with `c d = 1` and `c² d` an integer. -/
axiom no_rational_multiple (d : ℤ) (hd : 2 ≤ d) :
    ¬ ∃ c : ℚ, c * (d : ℚ) = 1 ∧ ∃ n : ℤ, c ^ 2 * (d : ℚ) = (n : ℚ)

end Lax894236.LinearSubspaceClass
end
