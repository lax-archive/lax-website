-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

-- Lax496464.ConsecutiveOnes
section
namespace Lax496464.ConsecutiveOnes

/-- The ones of each row occupy a consecutive block of columns. -/
def HasConsecutiveOnes {m n : Type*} [LE n] (A : Matrix m n ℤ) : Prop :=
  (∀ r c, A r c = 0 ∨ A r c = 1) ∧
    ∀ r c₁ c c₂, c₁ ≤ c → c ≤ c₂ → A r c₁ = 1 → A r c₂ = 1 → A r c = 1

end Lax496464.ConsecutiveOnes
end
