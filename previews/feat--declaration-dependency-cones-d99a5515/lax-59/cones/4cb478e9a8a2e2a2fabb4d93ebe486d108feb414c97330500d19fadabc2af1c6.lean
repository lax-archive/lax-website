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

/-- The number called `qPrev` is the last prime strictly before `q`. -/
def PrevPrime (qPrev q : ℕ) : Prop :=
  qPrev.Prime ∧ qPrev < q ∧ ∀ r, r.Prime → r < q → r ≤ qPrev

/-- The neighboring-prime factorization property from issue #6091. -/
def Interesting (n : ℕ) : Prop :=
  ∃ p q pNext qPrev : ℕ,
    p.Prime ∧ q.Prime ∧ p ≠ q ∧
    NextPrime p pNext ∧ PrevPrime qPrev q ∧
    n = p * q ∧ n + 1 = pNext * qPrev

end Lax59.InterestingNumbers
end
