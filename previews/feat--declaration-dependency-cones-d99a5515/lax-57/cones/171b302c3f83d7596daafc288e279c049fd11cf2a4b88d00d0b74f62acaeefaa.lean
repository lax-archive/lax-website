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

/-- The neighbors of `v` lying in a prescribed finite set. -/
def neighborsIn {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) (v : V) : Finset V :=
  A.filter fun x ↦ G.Adj v x

/-- `B` is `1/E`-sparse to `A`, with the denominator cleared. -/
def ESparseTo {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (B A : Finset V) : Prop :=
  ∀ b ∈ B, E * (neighborsIn G A b).card ≤ A.card

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

-- Lax57.PreparedHouseBlockade
section
namespace Lax57.PreparedHouseBlockade

open Finset

open scoped SimpleGraph

open Lax57.GraphDefinitions

universe u

/-- A very long equal-width blockade whose noncomplete pairs are sparse in
both vertexwise directions, or the desired complete blockade already. -/
axiom prepared_house_blockade :
    ∃ d : ℕ, 40 ≤ d ∧
      ∀ Q : ℕ, 8 ≤ Q →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
          IsHouseFree G → Q ^ (30 * d ^ 3) ≤ S.card →
            ( (∃ C : Blockade (V := V) Q,
                  C.IsInside S ∧ C.IsComplete G ∧
                    ∀ i : Fin Q,
                      S.card ≤ Q ^ (33 * d ^ 3) * (C.block i).card) ∨
              (∃ (m : ℕ) (B : Blockade (V := V) (Q ^ (4 * d))),
                  0 < m ∧ B.IsInside S ∧
                    (∀ i, m ≤ (B.block i).card ∧
                      (B.block i).card ≤ 8 * Q ^ 2 * m) ∧
                    (∀ i, (Gᶜ.induce (B.block i : Set V)).Connected) ∧
                    (∀ {i j}, i ≠ j →
                      ((∀ x ∈ B.block i, ∀ y ∈ B.block j, G.Adj x y) ∨
                        (ESparseTo G (Q ^ (4 * d)) (B.block i) (B.block j) ∧
                         ESparseTo G (Q ^ (4 * d)) (B.block j) (B.block i)))) ∧
                    Q * (∑ i, (B.block i).card) ≤ S.card ∧
                    S.card ≤ Q ^ (30 * d ^ 3) * m) )

end Lax57.PreparedHouseBlockade
end
