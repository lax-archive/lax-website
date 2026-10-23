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

/-- The neighbors of `v` lying in a prescribed finite set. -/
def neighborsIn {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) (v : V) : Finset V :=
  A.filter fun x ↦ G.Adj v x

/-- `B` is `1/E`-sparse to `A`, with the denominator cleared. -/
def ESparseTo {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (B A : Finset V) : Prop :=
  ∀ b ∈ B, E * (neighborsIn G A b).card ≤ A.card

/-- The pair `(A,B)` has edge density at most `1/E`. -/
def WeaklyESparse {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (A B : Finset V) : Prop :=
  E * (G.interedges A B).card ≤ A.card * B.card

/-- A sequence of pairwise disjoint vertex blocks. -/
structure Blockade {V : Type u} [DecidableEq V] (k : ℕ) where
  block : Fin k → Finset V
  disjoint : ∀ {i j : Fin k}, i ≠ j → Disjoint (block i) (block j)

/-- Each pair is complete or weakly `1/E`-sparse. -/
def Blockade.IsSemisparse {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (E : ℕ)
    (B : Blockade (V := V) k) : Prop :=
  ∀ {i j : Fin k}, i ≠ j →
    ((∀ x ∈ B.block i, ∀ y ∈ B.block j, G.Adj x y) ∨
      WeaklyESparse G E (B.block i) (B.block j))

end Lax57.GraphDefinitions
end

-- Lax57.BlockadeThinning
section
namespace Lax57.BlockadeThinning

open Lax57.GraphDefinitions

universe u

/-- Thin every block simultaneously and convert weak pair density to
vertexwise sparsity. -/
axiom semisparse_blockade_thinning :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (k P E t : ℕ) (B : Blockade (V := V) k),
      2 ≤ k → 2 * k ≤ t → 128 * k ^ 3 * E ≤ P →
      (∀ i, 2 * t ≤ (B.block i).card) → B.IsSemisparse G P →
        ∃ C : Blockade (V := V) k,
          (∀ i, C.block i ⊆ B.block i) ∧
          (∀ i, t ≤ 2 * (C.block i).card ∧ (C.block i).card ≤ t) ∧
          (∀ {i j}, i ≠ j →
            ((∀ x ∈ C.block i, ∀ y ∈ C.block j, G.Adj x y) ∨
              (ESparseTo G E (C.block i) (C.block j) ∧
               ESparseTo G E (C.block j) (C.block i))))

end Lax57.BlockadeThinning
end
