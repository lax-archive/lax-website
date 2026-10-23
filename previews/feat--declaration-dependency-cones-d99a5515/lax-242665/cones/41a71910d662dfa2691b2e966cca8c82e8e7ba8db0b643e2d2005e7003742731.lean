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

-- Lax242665.TwinPrimes
section
namespace Lax242665.TwinPrimes

/-- Beyond every natural number `n` lies a prime `p` with `p + 2` prime as
well. -/
axiom exists_twin_prime_gt :
    ∀ n : ℕ, ∃ p : ℕ, Primes.Prime p ∧ Primes.Prime (p + 2) ∧ n < p

end Lax242665.TwinPrimes
end
