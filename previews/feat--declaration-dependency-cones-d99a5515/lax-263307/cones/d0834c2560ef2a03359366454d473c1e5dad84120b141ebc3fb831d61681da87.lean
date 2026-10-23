-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

-- Lax263307.LinearRelaxation
section
namespace Lax263307.LinearRelaxation.IsFeasible
end Lax263307.LinearRelaxation.IsFeasible

namespace Lax263307.LinearRelaxation

/-- A certified upper bound on independent sets contained in a vertex set. -/
def IsIndependenceBound {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (u : ℕ) : Prop :=
  ∀ J : Finset (Fin n), J ⊆ C → G.IsIndepSet (J : Set (Fin n)) → J.card ≤ u

end Lax263307.LinearRelaxation
end
