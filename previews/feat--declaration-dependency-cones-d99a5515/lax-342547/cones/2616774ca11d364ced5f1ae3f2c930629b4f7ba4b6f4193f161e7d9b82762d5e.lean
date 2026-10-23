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

open scoped BigOperators

noncomputable def tailSum (a : ℕ → ℝ) (s b : ℕ) : ℝ := ∑ t ∈ Finset.range b, a (s-b+t)

noncomputable def tailDeficit (a : ℕ → ℝ) (s b : ℕ) : ℝ := a (s-b)-tailSum a s b/b

end Lax342547.DyadicTails
end

-- Lax342547.DyadicScale
section
namespace Lax342547.DyadicScale

open Lax342547.DyadicTails

open scoped BigOperators

axiom dyadic_small_tail (a : ℕ → ℝ) (ha : Antitone a) (ha0 : ∀ t, 0 ≤ a t)
    (k n : ℕ) (r : ℝ) (hnk : n ≤ k) (har : a 0 ≤ r) (hn : 8*r < n) :
    ∃ j < n, tailDeficit a (2^k) (2^(k-j)) < 1/4

end Lax342547.DyadicScale
end
