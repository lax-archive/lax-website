-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Lattice.Nat

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

-- Lax183560.Pathwidth
section
namespace Lax183560.Pathwidth

open Lax183560.PathDecomposition

/-- Existence of a path decomposition with bags of size at most `k + 1`. -/
def HasPathwidthAtMost {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : PathDecomposition G, ∀ i, (D.bag i).card ≤ k + 1

end Lax183560.Pathwidth
end
