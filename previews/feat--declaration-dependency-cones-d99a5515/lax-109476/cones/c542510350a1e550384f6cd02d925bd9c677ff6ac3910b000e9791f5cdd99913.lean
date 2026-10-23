-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

-- Lax109476.FourierMotzkin
section
namespace Lax109476.FourierMotzkin

/-- Eliminate the last variable using nonnegative row combinations. -/
axiom exists_elimination :
  ∀ (m : Type) [Fintype m] (n : ℕ)
    (A : Matrix m (Fin (n + 1)) ℝ) (b : m → ℝ),
    ∃ κ : Type, ∃ _ : Fintype κ, ∃ M : Matrix κ m ℝ,
      (∀ i j, 0 ≤ M i j) ∧
      (∀ i, (M * A) i (Fin.last n) = 0) ∧
      (∀ x' : Fin n → ℝ,
        (M * (A.submatrix id Fin.castSucc)).mulVec x' ≤ M.mulVec b ↔
          ∃ t : ℝ, A.mulVec (Fin.lastCases t x') ≤ b)

end Lax109476.FourierMotzkin
end
