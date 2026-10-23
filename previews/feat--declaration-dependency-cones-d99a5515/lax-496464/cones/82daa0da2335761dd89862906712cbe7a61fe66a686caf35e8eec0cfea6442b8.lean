-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec

-- Lax496464.WH_A6_ComputableBounds
section
namespace Lax496464.WH_A6_ComputableBounds

/-- Fixed powers of computable functions are computable. -/
axiom computable_pow {f : ℕ → ℕ} (e : ℕ) : Computable f → Computable fun k => f k ^ e

end Lax496464.WH_A6_ComputableBounds
end
