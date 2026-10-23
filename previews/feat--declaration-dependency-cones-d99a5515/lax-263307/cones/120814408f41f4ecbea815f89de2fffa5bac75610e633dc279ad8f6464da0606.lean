-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Size
import Mathlib.LinearAlgebra.Matrix.PosDef

-- Lax263307.BufferedEllipsoid
section
namespace Lax263307.BufferedEllipsoid

open Matrix

def scale {K : Type} [Field K] {n : ℕ} (z : Fin n → K) : Fin n → K := fun i => z i / (4 * (n : K))

end Lax263307.BufferedEllipsoid
end

-- Lax263307.RationalCutBuffer
section
namespace Lax263307.RationalCutBuffer

open BufferedEllipsoid (scale)

open Matrix

axiom central_buffer {n : ℕ} (a x z perturbed : Fin n → ℝ) (α Δ ρ L : ℝ)
    (nonnegative : 0 ≤ ρ) (norm : (∑ i, |a i|) ≤ L)
    (valid : a ⬝ᵥ z ≤ α) (gap : α + Δ ≤ a ⬝ᵥ x)
    (small : L * ρ ≤ Δ / 2) (near : ∀ i, |perturbed i - z i| ≤ ρ) :
    a ⬝ᵥ perturbed ≤ a ⬝ᵥ x - Δ / 2

end Lax263307.RationalCutBuffer
end
