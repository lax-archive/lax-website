-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.Matrix.PosDef

-- Lax263307.BufferedEllipsoid
section
namespace Lax263307.BufferedEllipsoid

open Matrix

def scale {K : Type} [Field K] {n : ℕ} (z : Fin n → K) : Fin n → K := fun i => z i / (4 * (n : K))

axiom initial_ball {n : ℕ} (positive : 0 < n) (z : Fin n → ℝ)
    (cube : ∀ i, 0 ≤ z i ∧ z i ≤ 1) (ρ : ℝ) (nonnegative : 0 ≤ ρ) (small : ρ ≤ 1 / 4)
    (e : Fin n → ℝ) (ball : e ⬝ᵥ e ≤ ρ ^ 2) :
    (scale z + e) ⬝ᵥ (scale z + e) ≤ 1

end Lax263307.BufferedEllipsoid
end
