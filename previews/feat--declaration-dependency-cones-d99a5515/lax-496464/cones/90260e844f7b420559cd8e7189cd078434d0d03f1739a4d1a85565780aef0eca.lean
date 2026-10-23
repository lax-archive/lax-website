-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec

-- Lax496464.WH_A6_ComputableBounds
section
namespace Lax496464.WH_A6_ComputableBounds

/-- Polynomials with natural coefficients are computable. -/
axiom computable_polynomial (p : Polynomial ℕ) : Computable fun k => p.eval k

end Lax496464.WH_A6_ComputableBounds
end
