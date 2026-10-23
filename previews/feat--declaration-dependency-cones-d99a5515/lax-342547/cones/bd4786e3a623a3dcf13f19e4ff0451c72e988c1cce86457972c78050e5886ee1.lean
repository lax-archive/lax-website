-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

-- Lax342547.DyadicDeficits
section
namespace Lax342547.DyadicDeficits

open scoped BigOperators

axiom sum_shift (v : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, v (j+1)) = (∑ j ∈ Finset.range n, v j)-v 0+v n

end Lax342547.DyadicDeficits
end
