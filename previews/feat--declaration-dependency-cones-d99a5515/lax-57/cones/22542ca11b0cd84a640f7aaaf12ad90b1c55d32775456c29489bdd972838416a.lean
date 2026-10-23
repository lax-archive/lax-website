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

/-- Every two different blocks are anticomplete to one another. -/
def Blockade.IsAnticomplete {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (B : Blockade (V := V) k) : Prop :=
  ∀ {i j : Fin k}, i ≠ j →
    ∀ x ∈ B.block i, ∀ y ∈ B.block j, ¬ G.Adj x y

/-- A complete or anticomplete blockade. -/
def Blockade.IsUniform {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (B : Blockade (V := V) k) : Prop :=
  B.IsComplete G ∨ B.IsAnticomplete G

/-- Every block lies in a prescribed ambient vertex set. -/
def Blockade.IsInside {V : Type u} [DecidableEq V] {k : ℕ}
    (B : Blockade (V := V) k) (S : Finset V) : Prop :=
  ∀ i : Fin k, B.block i ⊆ S

end Lax57.GraphDefinitions
end

-- Lax57.SparseHouseAcceleration
section
namespace Lax57.SparseHouseAcceleration

open Lax57.GraphDefinitions

universe u

/-- The sparse-house acceleration step, in reciprocal-square form. -/
axiom sparse_house_acceleration :
    ∃ d : ℕ, 2 ≤ d ∧
      ∀ R : ℕ, 64 ≤ R →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
          IsHouseFree G → ESparse G (R ^ 2) S →
            (∃ T : Finset V, T ⊆ S ∧
                S.card ≤ R ^ (32 * d ^ 3) * T.card ∧
                  ESparse G (R ^ (2 * d)) T) ∨
              (∃ B : Blockade (V := V) R,
                B.IsInside S ∧ B.IsUniform G ∧
                  ∀ i : Fin R,
                    S.card ≤ R ^ (36 * d ^ 3) * (B.block i).card)

end Lax57.SparseHouseAcceleration
end
