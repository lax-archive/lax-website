-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

-- Lax712553.QuadraticTwist
section
namespace Lax712553.QuadraticTwist

/-- The trace of Frobenius of `E_n : y² = x³ − n² x` at the prime `p`, as the
character sum `−∑_x χ(x³ − n² x)`. -/
noncomputable def a_p (n : ℤ) (p : ℕ) [Fact p.Prime] : ℤ :=
  -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (n : ZMod p) ^ 2 * x)

end Lax712553.QuadraticTwist
end
