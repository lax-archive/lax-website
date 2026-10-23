-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.Matrix.PosDef

-- Lax263307.BufferedEllipsoid
section
namespace Lax263307.BufferedEllipsoid

open Matrix

axiom coordinate_ball_bound {n : ℕ} (e : Fin n → ℝ) (ρ : ℝ) (nonnegative : 0 ≤ ρ)
    (ball : e ⬝ᵥ e ≤ ρ ^ 2) : ∀ i, |e i| ≤ ρ

end Lax263307.BufferedEllipsoid
end
