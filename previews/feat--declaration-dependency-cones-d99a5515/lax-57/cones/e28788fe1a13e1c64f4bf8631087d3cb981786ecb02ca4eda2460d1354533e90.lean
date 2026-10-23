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

/-- One of the two complementary graphs induced by `A` is `1/E`-sparse. -/
def ERestricted {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (A : Finset V) : Prop :=
  ESparse G E A ∨ ESparse Gᶜ E A

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

/-- All blocks have size at least `|V(G)| / loss`. -/
def Blockade.HasWidthLoss {V : Type u} [Fintype V] [DecidableEq V]
    {k : ℕ} (B : Blockade (V := V) k) (loss : ℕ) : Prop :=
  ∀ i : Fin k, Fintype.card V ≤ loss * (B.block i).card

/-- A uniform blockade with polynomial width and controlled length. -/
def HasUniformBlockade {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (E a : ℕ) : Prop :=
  ∃ (k : ℕ) (B : Blockade (V := V) k),
    2 ≤ k ∧ k ≤ E ∧ B.IsUniform G ∧ B.HasWidthLoss (k ^ a)

end Lax57.GraphDefinitions
end

-- Lax57.HouseDichotomy
section
namespace Lax57.HouseDichotomy

open Lax57.GraphDefinitions

universe u

/-- The structural dichotomy for finite house-free graphs. -/
axiom house_dichotomy :
    ∃ a : ℕ, 1 ≤ a ∧
      ∀ E : ℕ, 3 ≤ E →
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj],
          IsHouseFree G →
            (∃ X : Finset V,
                Fintype.card V ≤ E ^ a * X.card ∧ ERestricted G E X) ∨
              HasUniformBlockade G E a

end Lax57.HouseDichotomy
end
