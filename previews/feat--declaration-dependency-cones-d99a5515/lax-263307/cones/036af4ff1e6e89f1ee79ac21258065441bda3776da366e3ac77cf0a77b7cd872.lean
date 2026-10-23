-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Floor

-- Lax263307.GraphClasses
section
namespace Lax263307.GraphClasses

/-- A class of finite simple graphs, represented on numbered vertex sets. -/
abbrev GraphClass := (n : ℕ) → Set (SimpleGraph (Fin n))

end Lax263307.GraphClasses
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

-- Lax263307.BlowUpClasses
section
namespace Lax263307.BlowUpClasses

open GraphClasses IndependentBlowUp

/-- Graphs obtained by independent blow-ups of members, allowing empty fibres. -/
def blowUpClass (C : GraphClass) : GraphClass :=
  fun m => {H | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ C n ∧
    ∃ projection : Fin m → Fin n,
      ∀ u v, H.Adj u v ↔ G.Adj (projection u) (projection v)}

/-- Relabeling the explicit copy graph places it in the blow-up closure. -/
axiom copy_graph_mem (C : GraphClass) {n : ℕ} (G : SimpleGraph (Fin n))
    (member : G ∈ C n) (copies : Fin n → ℕ) (m : ℕ) (labeling : Fin m ≃ Vertex copies) :
    (graph G copies).comap labeling ∈ blowUpClass C m

end Lax263307.BlowUpClasses
end
