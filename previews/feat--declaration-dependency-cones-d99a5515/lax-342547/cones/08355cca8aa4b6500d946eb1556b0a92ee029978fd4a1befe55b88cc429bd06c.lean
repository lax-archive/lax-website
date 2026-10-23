-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

-- Lax342547.DyadicDeficits
section
namespace Lax342547
end Lax342547

namespace Lax342547.DyadicDeficits
end Lax342547.DyadicDeficits
end

-- Lax342547.DyadicTails
section
namespace Lax342547.DyadicTails
end Lax342547.DyadicTails
end

-- Lax342547.DyadicScale
section
namespace Lax342547.DyadicScale

open Lax342547.DyadicTails

open scoped BigOperators

axiom single_scale (f v : ℕ → ℝ) (n : ℕ) (r : ℝ)
    (hrec : ∀ j < n, 2*v j ≤ 2*(f j-f (j+1))+v (j+1))
    (hf0 : f 0 ≤ r) (hfn : 0 ≤ f n) (hv0 : 0 ≤ v 0) (hvn : v n ≤ f n)
    (hn : 8*r < n) : ∃ j < n, v j < 1/4

end Lax342547.DyadicScale
end
