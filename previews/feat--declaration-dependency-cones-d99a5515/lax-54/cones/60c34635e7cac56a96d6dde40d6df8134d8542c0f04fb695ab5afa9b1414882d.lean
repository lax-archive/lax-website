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

-- Lax54.KeyCombLemma
section
namespace Lax54.KeyCombLemma

open Lax54.GraphDefinitions

universe u

/-- The absolute constant in the integral form of the key comb lemma. -/
def keyCombConstant : ℕ := 2 ^ 20

/-- A sufficient lower bound on the sparsity parameter for obtaining at least two teeth. -/
def keySparsityThreshold : ℕ := 2 * keyCombConstant

/-- Lemma 3.1, with reciprocal integer parameters and cleared denominators. -/
axiom key_comb_lemma :
    ∀ E D Q : ℕ, keySparsityThreshold ≤ E → 0 < D →
      ∃ q : ℕ, 3 ≤ q ∧ Q ≤ q ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V),
          IsQCritical q G →
          Fintype.card V ≤ D * X.card →
          (∀ x : {v : V // v ∈ X},
            E * (G.induce (X : Set V)).degree x < X.card) →
          ∃ (t : ℕ) (C : StableHubComb G t),
            E ≤ keyCombConstant * t ∧
              ∀ i : Fin t,
                E * X.card ≤ keyCombConstant * t ^ 2 * (C.block i).card

end Lax54.KeyCombLemma
end
