-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Hasse

-- Lax54.GraphDefinitions
section
namespace Lax54
end Lax54

namespace Lax54.GraphDefinitions
end Lax54.GraphDefinitions

namespace Lax54.GraphDefinitions.StableHubComb
end Lax54.GraphDefinitions.StableHubComb
end

-- Lax57.GraphDefinitions
section
open Finset

open scoped SimpleGraph

namespace Lax57.GraphDefinitions

universe u

/-- The path on five vertices. -/
abbrev P5 : SimpleGraph (Fin 5) := SimpleGraph.pathGraph 5

/-- The house graph, namely the complement of the five-vertex path. -/
abbrev House : SimpleGraph (Fin 5) := P5ᶜ

/-- A graph has no induced copy of the house. -/
def IsHouseFree {V : Type u} (G : SimpleGraph V) : Prop :=
  ¬ House ⊴ G

/-- The graph induced by `A` has maximum degree at most `|A|/E`. -/
def ESparse {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (A : Finset V) : Prop :=
  ∀ v : {x : V // x ∈ A}, E * (G.induce (A : Set V)).degree v ≤ A.card

/-- A sequence of pairwise disjoint vertex blocks. -/
structure Blockade {V : Type u} [DecidableEq V] (k : ℕ) where
  block : Fin k → Finset V
  disjoint : ∀ {i j : Fin k}, i ≠ j → Disjoint (block i) (block j)

/-- Every two different blocks are complete to one another. -/
def Blockade.IsComplete {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (B : Blockade (V := V) k) : Prop :=
  ∀ {i j : Fin k}, i ≠ j →
    ∀ x ∈ B.block i, ∀ y ∈ B.block j, G.Adj x y

/-- Every block lies in a prescribed ambient vertex set. -/
def Blockade.IsInside {V : Type u} [DecidableEq V] {k : ℕ}
    (B : Blockade (V := V) k) (S : Finset V) : Prop :=
  ∀ i : Fin k, B.block i ⊆ S

end Lax57.GraphDefinitions
end

-- Lax57.SparseHouseTrichotomy
section
namespace Lax57.SparseHouseTrichotomy

open Lax57.GraphDefinitions

universe u

/-- Sparse refinement, a complete blockade, or an anticomplete peel. -/
axiom sparse_house_trichotomy :
    ∃ d : ℕ, 40 ≤ d ∧
      ∀ Q : ℕ, 8 ≤ Q →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
          IsHouseFree G → ESparse G Q S →
            ( (∃ T : Finset V, T ⊆ S ∧
                  S.card ≤ Q ^ (30 * d ^ 3) * T.card ∧
                    ESparse G (Q ^ (2 * d)) T) ∨
              (∃ B : Blockade (V := V) Q,
                  B.IsInside S ∧ B.IsComplete G ∧
                    ∀ i : Fin Q,
                      S.card ≤ Q ^ (33 * d ^ 3) * (B.block i).card) ∨
              (∃ X Y : Finset V,
                  X ⊆ S ∧ Y ⊆ S ∧ Disjoint X Y ∧
                    (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) ∧
                    S.card ≤ Q ^ (33 * d ^ 3) * X.card ∧
                    Q * (S.card - Y.card) ≤ 3 * S.card) )

end Lax57.SparseHouseTrichotomy
end
