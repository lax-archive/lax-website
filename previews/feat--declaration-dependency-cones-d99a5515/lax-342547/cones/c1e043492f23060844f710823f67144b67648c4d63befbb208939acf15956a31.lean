-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

-- Lax342547.DyadicDeficits
section
namespace Lax342547.DyadicDeficits

open scoped BigOperators

axiom deficit_ratio_sum (f v : ℕ → ℝ) (n : ℕ) (r : ℝ)
    (hrec : ∀ j < n, 2*v j ≤ 2*(f j-f (j+1))+v (j+1))
    (hf0 : f 0 ≤ r) (hfn : 0 ≤ f n) (hv0 : 0 ≤ v 0) (hvn : v n ≤ f n) :
    (∑ j ∈ Finset.range n, v j) ≤ 2*r

end Lax342547.DyadicDeficits
end
