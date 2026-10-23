-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy

-- Lax54.GraphDefinitions
section
namespace Lax54
end Lax54

namespace Lax54.GraphDefinitions
end Lax54.GraphDefinitions

namespace Lax54.GraphDefinitions.StableHubComb
end Lax54.GraphDefinitions.StableHubComb
end

-- Lax54.BipartiteCombLemma
section
namespace Lax54.BipartiteCombLemma

universe u

/--
A comb with distinct teeth in `A` and pairwise disjoint blocks in `B`. Each
tooth is adjacent to its own block and nonadjacent to every other block.
-/
structure CombBetween {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (t : ℕ) where
  tooth : Fin t → V
  block : Fin t → Finset V
  tooth_mem : ∀ i, tooth i ∈ A
  tooth_injective : Function.Injective tooth
  block_subset : ∀ i, block i ⊆ B
  blocks_disjoint : ∀ {i j}, i ≠ j → Disjoint (block i) (block j)
  tooth_adj_block : ∀ i, ∀ x ∈ block i, G.Adj (tooth i) x
  tooth_nonadj_other : ∀ {i j}, i ≠ j →
    ∀ x ∈ block j, ¬ G.Adj (tooth i) x

/-- The sparse alternative in the `d = 1/2` case of Theorem 2.1. -/
def SmallSideBound (C Gamma Delta b : ℕ) : Prop :=
  b ^ 2 ≤ C ^ 2 * Gamma * Delta

/-- The `d = 1/2` case of Theorem 2.1, with denominators cleared. -/
axiom bipartite_comb_lemma :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (A B : Finset V) (Gamma Delta : ℕ),
      Disjoint A B → 0 < Gamma →
      (∀ b ∈ B, ∃ a ∈ A, G.Adj a b) →
      (∀ a ∈ A, (B.filter fun b ↦ G.Adj a b).card ≤ Delta) →
      (∃ (t : ℕ) (Cmb : CombBetween G A B t),
          0 < t ∧ ∀ i : Fin t, Gamma ≤ t ^ 2 * (Cmb.block i).card) ∨
        SmallSideBound 128 Gamma Delta B.card

end Lax54.BipartiteCombLemma
end
