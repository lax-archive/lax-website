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

/-- A sequence of pairwise disjoint vertex blocks. -/
structure Blockade {V : Type u} [DecidableEq V] (k : ℕ) where
  block : Fin k → Finset V
  disjoint : ∀ {i j : Fin k}, i ≠ j → Disjoint (block i) (block j)

/-- The directed vertexwise sparsity condition of the paper. -/
def Blockade.IsESparse {V : Type u} [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (E : ℕ)
    (B : Blockade (V := V) k) : Prop :=
  ∀ {i j : Fin k}, i < j → ESparseTo G E (B.block j) (B.block i)

end Lax57.GraphDefinitions
end
