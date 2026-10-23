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

/-- The Euler characteristic of `X_d^n` in binomial form,
`∑_{j=1}^{n+1} (-1)^(j+1) C(n+2, j+1) d^j`, as an integer polynomial in `d`. -/
def chiBinom (n : ℕ) (d : ℤ) : ℤ :=
  ∑ j ∈ Icc 1 (n + 1), (-1 : ℤ) ^ (j + 1) * ((n + 2).choose (j + 1) : ℤ) * d ^ j

/-- In every odd dimension the Euler characteristic is even, for every degree. -/
axiom two_dvd_chiBinom_of_odd (n : ℕ) (hn : Odd n) (d : ℤ) : (2 : ℤ) ∣ chiBinom n d

end Lax894236.Parity
end
