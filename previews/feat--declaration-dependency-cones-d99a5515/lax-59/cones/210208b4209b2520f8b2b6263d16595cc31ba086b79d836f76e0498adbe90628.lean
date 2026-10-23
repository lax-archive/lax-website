-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib

-- Lax59.InterestingNumbers
section
namespace Lax59.InterestingNumbers

/-- The number called `pNext` is the first prime strictly after `p`. -/
def NextPrime (p pNext : ℕ) : Prop :=
  pNext.Prime ∧ p < pNext ∧ ∀ r, r.Prime → p < r → pNext ≤ r

end Lax59.InterestingNumbers
end
