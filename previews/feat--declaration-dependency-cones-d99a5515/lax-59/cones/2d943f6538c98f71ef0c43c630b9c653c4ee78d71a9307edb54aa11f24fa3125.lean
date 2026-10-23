-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib

-- Lax59.InterestingNumbers
section
namespace Lax59.InterestingNumbers

/-- The number called `qPrev` is the last prime strictly before `q`. -/
def PrevPrime (qPrev q : ℕ) : Prop :=
  qPrev.Prime ∧ qPrev < q ∧ ∀ r, r.Prime → r < q → r ≤ qPrev

end Lax59.InterestingNumbers
end
