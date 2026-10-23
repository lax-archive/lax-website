-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.Matrix.PosDef

-- Lax263307.BufferedEllipsoid
section
namespace Lax263307.BufferedEllipsoid

open Matrix

axiom integer_normal_norm {n : ℕ} (a : Fin n → ℤ) (nonzero : ∃ i, a i ≠ 0) :
    1 ≤ (fun i => (a i : ℝ)) ⬝ᵥ (fun i => (a i : ℝ))

end Lax263307.BufferedEllipsoid
end
