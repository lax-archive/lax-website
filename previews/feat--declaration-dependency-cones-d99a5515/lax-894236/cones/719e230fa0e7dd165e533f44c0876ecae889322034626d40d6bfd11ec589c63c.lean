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

/-- General type: for `d ≥ n + 3` the geometric genus is at least `2`. -/
axiom two_le_pg (m n : ℕ) (h : n + 2 ≤ m) : 2 ≤ pg m n

end Lax894236.GeometricGenus
end
