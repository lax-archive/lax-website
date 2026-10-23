-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

-- Lax263307.LinearRelaxation
section
namespace Lax263307
end Lax263307

namespace Lax263307.LinearRelaxation
end Lax263307.LinearRelaxation

namespace Lax263307.LinearRelaxation.IsFeasible
end Lax263307.LinearRelaxation.IsFeasible
end

-- Lax263307.TargetSearch
section
namespace Lax263307.TargetSearch

/-- Try positive targets in decreasing order, falling back to the empty set. -/
def search {n : ℕ} (attempt : ℕ → Option (Finset (Fin n))) :
    ℕ → Finset (Fin n) × ℕ
  | 0 => (∅, 0)
  | k + 1 => match attempt (k + 1) with
    | some I => (I, k + 1)
    | none => search attempt k

end Lax263307.TargetSearch
end
