-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Choose.Basic

-- Lax894236.GeometricGenus
section
namespace Lax894236.GeometricGenus

/-- The geometric genus `h^{n,0}` of a smooth hypersurface of degree `m + 1` and
dimension `n`, by Griffiths' formula: `C(m, n+1)`. -/
def pg (m n : ℕ) : ℕ := m.choose (n + 1)

end Lax894236.GeometricGenus
end

-- Lax894236.NoetherLefschetzWindow
section
namespace Lax894236.NoetherLefschetzWindow

open Lax894236.GeometricGenus

/-- The lower bound `d - 3` never exceeds `p_g` for `d ≥ 3`. -/
axiom bound_le_pg (m : ℕ) (hm : 2 ≤ m) : m - 2 ≤ pg m 2

end Lax894236.NoetherLefschetzWindow
end
