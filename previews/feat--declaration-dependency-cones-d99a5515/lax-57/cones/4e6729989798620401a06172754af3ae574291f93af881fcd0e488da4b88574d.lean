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

/-- Every block lies in a prescribed ambient vertex set. -/
def Blockade.IsInside {V : Type u} [DecidableEq V] {k : ℕ}
    (B : Blockade (V := V) k) (S : Finset V) : Prop :=
  ∀ i : Fin k, B.block i ⊆ S

end Lax57.GraphDefinitions
end

-- Lax57.AnticomponentBlockade
section
namespace Lax57.AnticomponentBlockade

open Lax57.GraphDefinitions

universe u

/-- A large anticonnected component or a long complete blockade. -/
axiom anticomponent_or_complete_blockade :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (Q : ℕ),
      2 ≤ Q →
        ( (∃ J : Finset V, J ⊆ T ∧
              (Gᶜ.induce (J : Set V)).Connected ∧
                T.card ≤ Q ^ 2 * J.card) ∨
          (∃ C : Blockade (V := V) Q,
              C.IsInside T ∧ C.IsComplete G ∧
                ∀ i : Fin Q,
                  T.card ≤ 4 * Q ^ 3 * (C.block i).card) )

end Lax57.AnticomponentBlockade
end
