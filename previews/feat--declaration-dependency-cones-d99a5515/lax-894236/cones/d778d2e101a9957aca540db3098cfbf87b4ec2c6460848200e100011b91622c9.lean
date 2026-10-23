-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

-- Lax894236.Parity
section
namespace Lax894236.Parity

open Finset

/-- Three times `h^{1,1}` of a smooth surface of degree `d` in `ℙ³`:
`2 d³ - 6 d² + 7 d`. -/
def h11Num (d : ℤ) : ℤ := 2 * d ^ 3 - 6 * d ^ 2 + 7 * d

/-- The Betti relation `χ = 2 + 2 h^{2,0} + h^{1,1}` holds for every degree, as
the polynomial identity `3 χ = 6 + (d-1)(d-2)(d-3) + 3 h^{1,1}`. -/
axiom betti_relation (d : ℤ) :
    3 * (d ^ 3 - 4 * d ^ 2 + 6 * d) = 6 + (d - 1) * (d - 2) * (d - 3) + h11Num d

end Lax894236.Parity
end
