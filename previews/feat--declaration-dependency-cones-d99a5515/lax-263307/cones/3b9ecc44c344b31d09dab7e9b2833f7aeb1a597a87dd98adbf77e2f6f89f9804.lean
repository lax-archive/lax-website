-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sublists
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

-- Lax263307.ExhaustiveTargets
section
namespace Lax263307.ExhaustiveTargets

/-- Enumerate the vertex sets of one prescribed cardinality. -/
def candidates (n k : ℕ) : List (Finset (Fin n)) :=
  ((List.finRange n).sublistsLen k).map List.toFinset

/-- Deterministic exact search at target `k`. -/
def findIndependentSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) : Option (Finset (Fin n)) :=
  (candidates n k).find? fun I => decide (G.IsIndepSet (I : Set (Fin n)))

/-- Search success is exact; search failure excludes every larger independent set. -/
axiom search_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
  match findIndependentSet G k with
  | some I => G.IsIndepSet (I : Set (Fin n)) ∧ I.card = k
  | none => ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card < k

end Lax263307.ExhaustiveTargets
end
