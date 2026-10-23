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

end Lax263307.ComponentCutEncoding
end

-- Lax263307.StrongComponentGaps
section
namespace Lax263307.StrongComponentGaps

open LinearRelaxation ComponentCutEncoding

axiom coefficient_l1 {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ) :
    (∑ B : Coordinate n r, |(coefficient A C u B : ℝ)|) ≤ C.card + u

end Lax263307.StrongComponentGaps
end
