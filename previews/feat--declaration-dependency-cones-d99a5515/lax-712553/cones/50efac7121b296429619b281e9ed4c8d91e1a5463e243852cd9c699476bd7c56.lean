-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval

-- Lax712553.TunnellParity
section
namespace Lax712553.TunnellParity

/-- The integer solutions of `a x² + y² + c z² = n` with coordinates in `[-n, n]`. -/
noncomputable def solutions (a c n : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-n) n) ×ˢ (Finset.Icc (-n) n) ×ˢ (Finset.Icc (-n) n)).filter
    (fun p => a * p.1 ^ 2 + p.2.1 ^ 2 + c * p.2.2 ^ 2 = n)

end Lax712553.TunnellParity
end
