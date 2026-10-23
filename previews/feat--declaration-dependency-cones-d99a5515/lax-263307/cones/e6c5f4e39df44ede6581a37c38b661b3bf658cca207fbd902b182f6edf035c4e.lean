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

def denominator {n : ℕ} (a : Fin n → ℚ) : ℕ := ∏ i, (a i).den

def integerNormal {n : ℕ} (a : Fin n → ℚ) (i : Fin n) : ℤ :=
  (a i).num * (denominator a / (a i).den : ℕ)

end Lax263307.RationalCutBuffer
end
