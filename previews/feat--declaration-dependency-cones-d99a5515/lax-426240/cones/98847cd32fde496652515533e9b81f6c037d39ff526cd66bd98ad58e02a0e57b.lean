-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

-- Lax426240.LcmDeterminant
section
namespace Lax426240.LcmDeterminant

open Finset

open scoped ArithmeticFunction.Moebius

/-- The Dirichlet inverse-image of `1/n` under convolution with `1`:
`g(n) = ∑_{ab = n} μ(a) / b`. -/
noncomputable def g (n : ℕ) : ℚ :=
  ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℚ) * (1 / x.2)

/-- `g(n) = (1/n) ∏_{p ∣ n} (1 − p)` for `n ≠ 0`. -/
axiom g_eq (n : ℕ) (hn : n ≠ 0) :
    g n = (1 / (n : ℚ)) * ∏ p ∈ n.primeFactors, (1 - (p : ℚ))

end Lax426240.LcmDeterminant
end
