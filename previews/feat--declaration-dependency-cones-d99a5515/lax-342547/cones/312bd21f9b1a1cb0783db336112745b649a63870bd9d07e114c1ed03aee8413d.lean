-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

-- Lax342547.DyadicDeficits
section
namespace Lax342547.DyadicDeficits

open scoped BigOperators

axiom two_mode_scale (fC fR vC vR : ℕ → ℝ) (n : ℕ) (r : ℝ)
    (hC : ∀ j < n, 2*vC j ≤ 2*(fC j-fC (j+1))+vC (j+1))
    (hR : ∀ j < n, 2*vR j ≤ 2*(fR j-fR (j+1))+vR (j+1))
    (hfC0 : fC 0 ≤ r) (hfR0 : fR 0 ≤ r)
    (hfCn : 0 ≤ fC n) (hfRn : 0 ≤ fR n)
    (hvC0 : 0 ≤ vC 0) (hvR0 : 0 ≤ vR 0)
    (hvCn : vC n ≤ fC n) (hvRn : vR n ≤ fR n) (hn : 16*r < n) :
    ∃ j < n, vC j+vR j < 1/4

end Lax342547.DyadicDeficits
end
