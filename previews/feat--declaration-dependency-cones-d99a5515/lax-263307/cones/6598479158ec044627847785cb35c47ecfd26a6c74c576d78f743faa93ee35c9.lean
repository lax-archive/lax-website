-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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

-- Lax263307.ComponentCuts
section
namespace Lax263307.ComponentCuts
end Lax263307.ComponentCuts
end

-- Lax263307.SeparatorComponents
section
namespace Lax263307.SeparatorComponents

/-- A partition of the undeleted vertices, closed under undeleted edges. -/
structure Partition {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (ι : Type) where
  /-- The original vertices in each part. -/
  vertices : ι → Finset (Fin n)
  /-- Parts exclude the deleted vertices. -/
  outside : ∀ i v, v ∈ vertices i → v ∉ S
  /-- Every undeleted vertex belongs to exactly one part. -/
  unique : ∀ v, v ∉ S → ∃! i, v ∈ vertices i
  /-- No undeleted edge leaves a part. -/
  closed : ∀ i u v, u ∈ vertices i → v ∉ S → G.Adj u v → v ∈ vertices i

/-- The recursive answer is the union of the answers on the parts. -/
def combine {n : ℕ} {ι : Type} [Fintype ι] (I : ι → Finset (Fin n)) :
    Finset (Fin n) := Finset.univ.biUnion I

end Lax263307.SeparatorComponents
end

-- Lax263307.RecursiveRounding
section
namespace Lax263307.RecursiveRounding

open LinearRelaxation SeparatorComponents

/-- Independent answers on different parts combine, and their sizes add. -/
axiom combine_independent {n : ℕ} {ι : Type} [Fintype ι]
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (P : Partition G S ι)
    (I : ι → Finset (Fin n)) (inside : ∀ i, I i ⊆ P.vertices i)
    (independent : ∀ i, G.IsIndepSet (I i : Set (Fin n))) :
    G.IsIndepSet (combine I : Set (Fin n)) ∧ (combine I).card = ∑ i, (I i).card

end Lax263307.RecursiveRounding
end
