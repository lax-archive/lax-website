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
