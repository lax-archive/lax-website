-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Floor

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307
end Lax263307

namespace Lax263307.WeightedIndependentSet
end Lax263307.WeightedIndependentSet

namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance
end

-- Lax263307.IndependentBlowUp
section
namespace Lax263307.IndependentBlowUp

/-- The vertices of an independent blow-up, including possibly empty fibres. -/
abbrev Vertex {n : ℕ} (copies : Fin n → ℕ) := (v : Fin n) × Fin (copies v)

/-- Copies are adjacent precisely when their original vertices are adjacent. -/
def graph {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ) :
    SimpleGraph (Vertex copies) := G.comap fun v => v.1

/-- All copies of a given original vertex set. -/
def lift {n : ℕ} (copies : Fin n → ℕ) (I : Finset (Fin n)) : Finset (Vertex copies) :=
  I.sigma fun _ => Finset.univ

end Lax263307.IndependentBlowUp
end

-- Lax263307.BlowUpIndependentSets
section
namespace Lax263307.BlowUpIndependentSets

open IndependentBlowUp

/-- Taking all copies preserves independence. -/
axiom lift_independent {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ)
    (I : Finset (Fin n)) (independent : G.IsIndepSet (I : Set (Fin n))) :
    (graph G copies).IsIndepSet (lift copies I : Set (Vertex copies))

end Lax263307.BlowUpIndependentSets
end
