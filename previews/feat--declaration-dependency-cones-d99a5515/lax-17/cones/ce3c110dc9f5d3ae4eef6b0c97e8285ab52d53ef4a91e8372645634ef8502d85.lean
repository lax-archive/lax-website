-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Finset.Sym

-- Lax17.Grid
section
namespace Lax17.Grid

/-- The canonical `g × g` square grid. -/
def squareGrid (g : ℕ) : SimpleGraph (Fin g × Fin g) :=
  SimpleGraph.pathGraph g □ SimpleGraph.pathGraph g

end Lax17.Grid
end

-- Lax17.Minor
section
namespace Lax17.Minor

universe u v

/-- Branch-set data witnessing that `H` is a minor of `G`. -/
structure Model {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set representing each vertex of `H`. -/
  branchSet : W → Set V
  /-- Every branch set is nonempty. -/
  branch_nonempty : ∀ w : W, (branchSet w).Nonempty
  /-- Every branch set induces a connected graph in `G`. -/
  branch_connected :
    ∀ w : W, (G.induce (branchSet w)).Connected
  /-- Branch sets representing distinct vertices are disjoint. -/
  branch_disjoint :
    ∀ ⦃x y : W⦄, x ≠ y → Disjoint (branchSet x) (branchSet y)
  /-- Every edge of `H` is represented by an edge between branch sets. -/
  adjacent :
    ∀ ⦃x y : W⦄, H.Adj x y →
      ∃ a ∈ branchSet x, ∃ b ∈ branchSet y, G.Adj a b

/-- `H` is a graph minor of `G`. -/
def IsMinor {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (Model H G)

end Lax17.Minor
end

-- Lax17.GridMinor
section
namespace Lax17.GridMinor

universe u

/-- `G` contains the `g × g` square grid as a minor. -/
def ContainsGridMinor {V : Type u} (G : SimpleGraph V) (g : ℕ) : Prop :=
  Lax17.Minor.IsMinor (Lax17.Grid.squareGrid g) G

end Lax17.GridMinor
end

-- Lax17.Paths
section
namespace Lax17.Paths.EdgeCutPartition
end Lax17.Paths.EdgeCutPartition

namespace Lax17.Paths.EdgeLinkage
end Lax17.Paths.EdgeLinkage

namespace Lax17.Paths

universe u

/-- A simple finite path in `G`, with its orientation recorded. -/
structure Path {V : Type u} (G : SimpleGraph V) where
  source : V
  target : V
  walk : G.Walk source target
  simple : walk.IsPath

namespace Path

/-- The finite set of vertices used by a path. -/
noncomputable def vertices {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) : Finset V :=
  P.walk.support.toFinset

/-- `P` is oriented from `A` to `B`. -/
def Connects {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (A B : Finset V) : Prop :=
  P.source ∈ A ∧ P.target ∈ B

/-- Every vertex of `P` lies in `C`. -/
def StaysIn {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (C : Finset V) : Prop :=
  P.vertices ⊆ C

/-- The internal vertices of `P` avoid `X`. -/
def InternallyAvoids {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (X : Finset V) : Prop :=
  ∀ v ∈ P.vertices, v ∈ X → v = P.source ∨ v = P.target

end Path

/-- Exactly `k` pairwise vertex-disjoint paths oriented from `A` to `B`. -/
structure VertexLinkage {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ) where
  path : Fin k → Path G
  connects : ∀ i : Fin k, (path i).Connects A B
  vertex_disjoint :
    Pairwise fun i j => Disjoint (path i).vertices (path j).vertices

/-- A path joining two members of a linkage whose internal vertices avoid
every path of that linkage. -/
structure VertexLinkage.BridgeBetween
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V} {k : ℕ}
    (P : VertexLinkage G A B k) (i j : Fin k) where
  path : Path G
  source_on_first : path.source ∈ (P.path i).vertices
  target_on_second : path.target ∈ (P.path j).vertices
  internally_avoids_rows :
    ∀ r : Fin k, path.InternallyAvoids (P.path r).vertices

/-- Every two distinct paths of the linkage have a bridge contained in `C`. -/
def VertexLinkage.HasPairwiseBridgesIn
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {A B : Finset V} {k : ℕ}
    (P : VertexLinkage G A B k) (C : Finset V) : Prop :=
  ∀ ⦃i j : Fin k⦄, i ≠ j →
    ∃ bridge : P.BridgeBetween i j, bridge.path.StaysIn C

end Lax17.Paths
end

-- Lax17.Linkedness
section
namespace Lax17.Linkedness

universe u

open Lax17.Paths

/-- `A` and `B` are node-linked by the maximum possible number of
vertex-disjoint paths contained in `C`. -/
def NodeLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C A B : Finset V) : Prop :=
  A ⊆ C ∧ B ⊆ C ∧ Disjoint A B ∧
    ∀ ⦃A' B' : Finset V⦄, A' ⊆ A → B' ⊆ B →
      ∃ P : VertexLinkage G A' B' (min A'.card B'.card),
        ∀ i : Fin (min A'.card B'.card), (P.path i).StaysIn C

end Lax17.Linkedness
end

-- Lax17.PathOfSets
section
namespace Lax17.PathOfSets.HairyClusterSplit
end Lax17.PathOfSets.HairyClusterSplit

namespace Lax17.PathOfSets.HairySystem
end Lax17.PathOfSets.HairySystem

namespace Lax17.PathOfSets.StrongSystem
end Lax17.PathOfSets.StrongSystem

namespace Lax17.PathOfSets.ThreeWayClusterSplit
end Lax17.PathOfSets.ThreeWayClusterSplit

namespace Lax17.PathOfSets

universe u

open Lax17.Linkedness

open Lax17.Paths

/-- A finite vertex set inducing a connected graph. -/
def IsCluster {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C : Finset V) : Prop :=
  (G.induce {v : V | v ∈ C}).Connected

namespace System

end System

end Lax17.PathOfSets
end

-- Lax17.LocalRoutingOrGrid
section
namespace Lax17.LocalRoutingOrGrid

universe u

/-- In one connected cluster, large linked terminal sets either force an
`h × h` grid minor or admit `q` disjoint routes with pairwise bridges. -/
axiom localRoutingOrGrid :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C A B : Finset V} {h q w : ℕ},
      1 < h →
        1 < q →
          Lax17.PathOfSets.IsCluster G C →
            Lax17.Linkedness.NodeLinkedIn G C A B →
              A.card = w →
                B.card = w →
                  (16 * h + 10) * q ≤ w →
                    Lax17.GridMinor.ContainsGridMinor G h ∨
                      ∃ Q : Lax17.Paths.VertexLinkage G A B q,
                        (∀ i : Fin q, (Q.path i).StaysIn C) ∧
                          Q.HasPairwiseBridgesIn C

end Lax17.LocalRoutingOrGrid
end
