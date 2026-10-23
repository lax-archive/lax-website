-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax183560.PathDecomposition
section
namespace Lax183560.PathDecomposition

/-- A path decomposition indexed by a finite linear order. -/
structure PathDecomposition {V : Type} (G : SimpleGraph V) where
  length : ℕ
  bag : Fin length → Finset V
  vertex_mem_bag : ∀ v : V, ∃ i, v ∈ bag i
  edge_mem_bag : ∀ ⦃u v : V⦄, G.Adj u v →
    ∃ i, u ∈ bag i ∧ v ∈ bag i
  bag_indices_interval : ∀ v : V, ∀ i j l : Fin length,
    (i ≤ j ∧ j ≤ l ∧ v ∈ bag i ∧ v ∈ bag l) → v ∈ bag j

end Lax183560.PathDecomposition
end
