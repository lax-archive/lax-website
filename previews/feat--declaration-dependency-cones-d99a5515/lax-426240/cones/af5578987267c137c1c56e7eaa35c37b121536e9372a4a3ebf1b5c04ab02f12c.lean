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

end Lax426240.LcmDeterminant
end
