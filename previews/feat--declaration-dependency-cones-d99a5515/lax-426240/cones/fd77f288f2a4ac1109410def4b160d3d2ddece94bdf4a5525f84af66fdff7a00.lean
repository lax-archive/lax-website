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

/-- The `N × N` matrix with entries `lcm(i, j)` for `1 ≤ i, j ≤ N`, over `ℚ`. -/
def lcmMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => (Nat.lcm ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ)

/-- The Dirichlet inverse-image of `1/n` under convolution with `1`:
`g(n) = ∑_{ab = n} μ(a) / b`. -/
noncomputable def g (n : ℕ) : ℚ :=
  ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℚ) * (1 / x.2)

/-- `det (lcm(i,j)) = (N!)² ∏_{k ≤ N} g(k)`. -/
axiom det_lcmMatrix (N : ℕ) :
    (lcmMatrix N).det
      = (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * ∏ i : Fin N, g ((i : ℕ) + 1)

end Lax426240.LcmDeterminant
end
