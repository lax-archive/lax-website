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

/-- The five-cycle. -/
abbrev C5 : SimpleGraph (Fin 5) := SimpleGraph.cycleGraph 5

/-- A graph has no induced copy of the five-cycle. -/
def IsC5Free {V : Type u} (G : SimpleGraph V) : Prop :=
  ¬ C5 ⊴ G

/-- The product `ω(G) · α(G)` used in the critical-graph argument. -/
noncomputable def kappa {V : Type u} (G : SimpleGraph V) : ℕ :=
  G.cliqueNum * G.indepNum

/--
A graph is `q`-critical if `kappa G ^ q < |V(G)|`, while every proper
vertex-induced subgraph `G[S]` satisfies `|S| ≤ kappa (G[S]) ^ q`.
-/
def IsQCritical {V : Type u} [Fintype V] (q : ℕ) (G : SimpleGraph V) : Prop :=
  kappa G ^ q < Fintype.card V ∧
    ∀ S : Finset V, S.card < Fintype.card V →
      S.card ≤ kappa (G.induce (S : Set V)) ^ q

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

-- Lax54.CriticalCombInput
section
open scoped SimpleGraph

namespace Lax54.CriticalCombInput

open Lax54.GraphDefinitions

universe u

/-- The quantitative critical-comb statement used in the proof of Theorem 4.4. -/
axiom exists_critical_comb_parameters :
    ∃ q A : ℕ, 3 ≤ q ∧ A ≤ 2 ^ (q - 2) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        IsC5Free G → IsQCritical q G →
          (∃ (t : ℕ) (C : StableHubComb G t),
              2 ≤ t ∧
                ∀ i : Fin t, Fintype.card V ≤ A * t ^ 2 * (C.block i).card) ∨
          (∃ (t : ℕ) (C : StableHubComb Gᶜ t),
              2 ≤ t ∧
                ∀ i : Fin t, Fintype.card V ≤ A * t ^ 2 * (C.block i).card)

end Lax54.CriticalCombInput
end
