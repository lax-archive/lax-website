-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy

-- Lax54.GraphDefinitions
section
open Finset

open scoped SimpleGraph

namespace Lax54.GraphDefinitions

universe u

/--
A comb whose teeth form a stable set, together with the hub vertex from
Lemma 3.1. The hub is adjacent to every tooth and nonadjacent to every block.
The tooth `a_i` is adjacent to its block `B_i` and nonadjacent to every other
block.
-/
structure StableHubComb {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) where
  tooth : Fin t → V
  block : Fin t → Finset V
  hub : V
  tooth_injective : Function.Injective tooth
  blocks_disjoint : ∀ {i j : Fin t}, i ≠ j → Disjoint (block i) (block j)
  tooth_not_mem : ∀ i j : Fin t, tooth i ∉ block j
  hub_not_mem : ∀ i : Fin t, hub ∉ block i
  tooth_adj_block : ∀ i : Fin t, ∀ x ∈ block i, G.Adj (tooth i) x
  tooth_nonadj_other : ∀ {i j : Fin t}, i ≠ j →
    ∀ x ∈ block j, ¬ G.Adj (tooth i) x
  teeth_stable : ∀ {i j : Fin t}, i ≠ j → ¬ G.Adj (tooth i) (tooth j)
  hub_adj_tooth : ∀ i : Fin t, G.Adj hub (tooth i)
  hub_nonadj_block : ∀ i : Fin t, ∀ x ∈ block i, ¬ G.Adj hub x

end Lax54.GraphDefinitions
end
