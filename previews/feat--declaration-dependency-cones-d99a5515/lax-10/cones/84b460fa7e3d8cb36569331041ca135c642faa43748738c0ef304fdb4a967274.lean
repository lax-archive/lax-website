-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

-- Lax10.ThreeConnectedAndColorable
section
open Finset

namespace Lax10.ThreeConnectedAndColorable

universe u

variable {V : Type u}

/-- A simple graph is colorable with at most $m$ colors. -/
def KColorable (m : Nat) (G : SimpleGraph V) : Prop :=
  G.Colorable m

/-- The induced graph obtained after deleting the vertices in $S$. -/
def deleteVertices (G : SimpleGraph V) (S : Finset V) :
    SimpleGraph {v : V // v ∉ S} :=
  G.induce {v : V | v ∉ S}

/-- The set $S$ separates two vertices that remain after its deletion. -/
def IsVertexSeparator (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ x y : {v : V // v ∉ S}, ¬ (deleteVertices G S).Reachable x y

/--
A graph is $3$-connected when it has at least 4 vertices and no vertex
separator of size at most two.
-/
def ThreeConnected (G : SimpleGraph V) : Prop :=
  4 ≤ Nat.card V ∧
    ∀ S : Finset V, S.card ≤ 2 → ¬ IsVertexSeparator G S

end Lax10.ThreeConnectedAndColorable
end

-- Lax10.Fragile
section
namespace Lax10.Fragile

universe u

variable {V : Type u}

open Lax10.ThreeConnectedAndColorable

/-- A graph is fragile when none of its subgraphs is $3$-connected. -/
def HasNoThreeConnectedSubgraph (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, ¬ ThreeConnected H.coe

end Lax10.Fragile
end

-- Lax10.FragileFourColorable
section
namespace Lax10.FragileFourColorable

universe u

open Lax10.ThreeConnectedAndColorable

open Lax10.Fragile

/-- Every finite simple graph with no $3$-connected subgraph is $4$-colorable. -/
axiom fragile_four_colorable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hfragile : HasNoThreeConnectedSubgraph G) :
    KColorable 4 G

end Lax10.FragileFourColorable
end
