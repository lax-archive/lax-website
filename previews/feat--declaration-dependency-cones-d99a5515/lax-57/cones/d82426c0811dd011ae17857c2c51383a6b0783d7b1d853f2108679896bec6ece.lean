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

/-- All blocks have size at least `|V(G)| / loss`. -/
def Blockade.HasWidthLoss {V : Type u} [Fintype V] [DecidableEq V]
    {k : ℕ} (B : Blockade (V := V) k) (loss : ℕ) : Prop :=
  ∀ i : Fin k, Fintype.card V ≤ loss * (B.block i).card

end Lax57.GraphDefinitions
end

-- Lax57.SemisparseBlockade
section
namespace Lax57.SemisparseBlockade

open Lax57.GraphDefinitions

universe u

/-- Polynomial semisparse blockades in house-free graphs. -/
axiom semisparse_house_blockade :
    ∃ d : ℕ, 40 ≤ d ∧
      ∀ E : ℕ, 2 ≤ E →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
          IsHouseFree G → E ^ (10 * d ^ 2) ≤ Fintype.card V →
            ∃ B : Blockade (V := V) E,
              B.IsSemisparse G (E ^ d) ∧
                B.HasWidthLoss (E ^ (10 * d ^ 2))

end Lax57.SemisparseBlockade
end
