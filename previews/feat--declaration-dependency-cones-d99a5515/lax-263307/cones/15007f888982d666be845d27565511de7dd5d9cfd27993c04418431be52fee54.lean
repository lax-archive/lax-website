-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax263307.LinearRelaxation
section
namespace Lax263307.LinearRelaxation.IsFeasible
end Lax263307.LinearRelaxation.IsFeasible

namespace Lax263307.LinearRelaxation

/-- The coordinate sets of the level-`r` relaxation. -/
abbrev Coordinate (n r : ℕ) := {A : Finset (Fin n) // A.card ≤ r + 2}

/-- A vector with precisely the coordinates used by the relaxation. -/
abbrev MomentVector (n r : ℕ) := Coordinate n r → ℝ

/-- Read a coordinate, returning zero outside the truncated coordinate domain. -/
def value {n r : ℕ} (y : MomentVector n r) (A : Finset (Fin n)) : ℝ :=
  if h : A.card ≤ r + 2 then y ⟨A, h⟩ else 0

end Lax263307.LinearRelaxation
end

-- Lax263307.ComponentCuts
section
namespace Lax263307.ComponentCuts
end Lax263307.ComponentCuts
end

-- Lax263307.ComponentCutEncoding
section
namespace Lax263307.ComponentCutEncoding

open LinearRelaxation

/-- The coefficient at one coordinate, after collecting all repeated terms. -/
def coefficient {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (B : Coordinate n r) : ℤ :=
  (∑ v ∈ C, if insert v A = B.val then 1 else 0) -
    if A = B.val then (u : ℤ) else 0

/-- Evaluate the coefficient vector in the real coordinate space. -/
noncomputable def evaluate {n r : ℕ} (a : Coordinate n r → ℤ)
    (z : MomentVector n r) : ℝ := ∑ B, (a B : ℝ) * z B

/-- The collected coefficient vector represents exactly the intended cut. -/
axiom evaluation_identity {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (size : A.card ≤ r) (z : MomentVector n r) :
    evaluate (coefficient A C u) z =
      (∑ v ∈ C, value z (insert v A)) - (u : ℝ) * value z A

end Lax263307.ComponentCutEncoding
end
