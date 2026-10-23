-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec

-- Lax496464.WH_A6_ComputableBounds
section
namespace Lax496464.WH_A6_ComputableBounds

/-- Every computable function is bounded by a computable nondecreasing function. -/
axiom exists_monotone_bound {f : ℕ → ℕ} :
    Computable f → ∃ g : ℕ → ℕ, Computable g ∧ Monotone g ∧ ∀ k, f k ≤ g k

end Lax496464.WH_A6_ComputableBounds
end
