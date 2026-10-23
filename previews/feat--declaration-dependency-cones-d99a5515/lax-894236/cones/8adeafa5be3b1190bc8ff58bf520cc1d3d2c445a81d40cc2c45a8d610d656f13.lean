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

/-- Calabi–Yau: the geometric genus is `1` if and only if `d = n + 2`. -/
axiom pg_eq_one_iff (m n : ℕ) : pg m n = 1 ↔ m = n + 1

end Lax894236.GeometricGenus
end
