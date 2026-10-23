-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Floor

-- Lax228581.Treewidth
section
namespace Lax228581
end Lax228581

namespace Lax228581.Treewidth
end Lax228581.Treewidth

namespace Lax228581.Treewidth.TreeDecomposition
end Lax228581.Treewidth.TreeDecomposition
end

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

end Lax263307.IndependentBlowUp
end

-- Lax263307.BlowUpIndependentSets
section
namespace Lax263307.BlowUpIndependentSets
end Lax263307.BlowUpIndependentSets
end

-- Lax263307.BlowUpDecompositions
section
namespace Lax263307.BlowUpDecompositions
end Lax263307.BlowUpDecompositions
end

-- Lax263307.BlowUpDeletion
section
namespace Lax263307.BlowUpDeletion

open scoped Classical

open IndependentBlowUp Lax228581.Treewidth

/-- The vertices removed at degree threshold `s`. -/
noncomputable def highDegree {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (s : ℕ) : Finset (Vertex copies) :=
  Finset.univ.filter fun v => s < (graph G copies).degree v

end Lax263307.BlowUpDeletion
end
