-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Notation

-- Lax242665.Primes
section
namespace Lax242665.Primes

/-- `n` is prime: it is greater than 1, and every divisor `d` of `n` is
`1` or `n` itself. -/
def Prime (n : ℕ) : Prop :=
  1 < n ∧ ∀ d : ℕ, d ∣ n → d = 1 ∨ d = n

end Lax242665.Primes
end

-- Lax771644.ExternalPrimes
section
namespace Lax771644.ExternalPrimes

/-- Beyond every natural number lies a prime, in the sense of `lax-242665`. -/
axiom e2_has_larger_prime : ∀ n : ℕ, ∃ p : ℕ, Lax242665.Primes.Prime p ∧ n < p

end Lax771644.ExternalPrimes
end
