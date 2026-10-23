-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Sym

-- Lax17.Degree
section
namespace Lax17.Degree

universe u

/-- `N` is the neighbourhood of `v` in `G`. -/
def IsNeighbourhood {V : Type u} (G : SimpleGraph V) (v : V)
    (N : Finset V) : Prop :=
  ∀ w : V, w ∈ N ↔ G.Adj v w

/-- The degree of `v` in `G` is at most `d`. -/
def AtMost {V : Type u} (G : SimpleGraph V) (v : V) (d : ℕ) : Prop :=
  ∃ N : Finset V, IsNeighbourhood G v N ∧ N.card ≤ d

/-- Every vertex of `G` has degree at most `d`. -/
def MaximumAtMost {V : Type u} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, AtMost G v d

end Lax17.Degree
end

-- Lax17.Paths
section
namespace Lax17.Paths.EdgeCutPartition
end Lax17.Paths.EdgeCutPartition

namespace Lax17.Paths.EdgeLinkage
end Lax17.Paths.EdgeLinkage

namespace Lax17.Paths.VertexLinkage.BridgeBetween
end Lax17.Paths.VertexLinkage.BridgeBetween

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

/-- `X` is node-well-linked inside `C`. -/
def NodeWellLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C X : Finset V) : Prop :=
  X ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ X → B ⊆ X → Disjoint A B →
      ∃ P : VertexLinkage G A B (min A.card B.card),
        ∀ i : Fin (min A.card B.card), (P.path i).StaysIn C

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

-- Lax17.TreeOfSets
section
namespace Lax17.TreeOfSets

universe u

open Lax17.Degree

open Lax17.Linkedness

open Lax17.PathOfSets

open Lax17.Paths

/-- A subcubic tree-of-sets system with `m` clusters and width `w`. -/
structure System {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (m w : ℕ) where
  clusterCount_pos : 0 < m
  width_pos : 0 < w
  metaTree : SimpleGraph (Fin m)
  meta_isTree : metaTree.IsTree
  meta_subcubic : MaximumAtMost metaTree 3
  cluster : Fin m → Finset V
  cluster_connected : ∀ i : Fin m, IsCluster G (cluster i)
  cluster_disjoint :
    ∀ ⦃i j : Fin m⦄, i ≠ j → Disjoint (cluster i) (cluster j)
  interface :
    (i j : Fin m) → metaTree.Adj i j → Finset V
  interface_subset :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j),
      interface i j hij ⊆ cluster i
  interface_card :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j),
      (interface i j hij).card = w
  incident_interfaces_disjoint :
    ∀ {i j k : Fin m} (hij : metaTree.Adj i j)
      (hik : metaTree.Adj i k),
        j ≠ k → Disjoint (interface i j hij) (interface i k hik)
  connector :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j),
      VertexLinkage G (interface i j hij)
        (interface j i (metaTree.symm.symm i j hij)) w
  connector_avoids_clusters :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j)
      (r : Fin m) (a : Fin w),
        ((connector i j hij).path a).InternallyAvoids (cluster r)
  connectors_disjoint :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j)
      (p q : Fin m) (hpq : metaTree.Adj p q),
        s(i, j) ≠ s(p, q) →
          ∀ a b : Fin w,
            Disjoint ((connector i j hij).path a).vertices
              ((connector p q hpq).path b).vertices

/-- A strong tree-of-sets system. -/
structure StrongSystem {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (m w : ℕ) extends System G m w where
  interface_well_linked :
    ∀ (i j : Fin m) (hij : metaTree.Adj i j),
      NodeWellLinkedIn G (cluster i) (interface i j hij)
  incident_interfaces_linked :
    ∀ {i j k : Fin m} (hij : metaTree.Adj i j)
      (hik : metaTree.Adj i k),
        j ≠ k →
          NodeLinkedIn G (cluster i)
            (interface i j hij) (interface i k hik)

/-- The meta-tree contains an ordered simple path with `ℓ` vertices. -/
def HasMetaPath {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {m w : ℕ}
    (T : StrongSystem G m w) (ℓ : ℕ) : Prop :=
  ∃ order : Fin ℓ → Fin m,
    Function.Injective order ∧
      ∀ (i : Fin ℓ) (hi : i.1 + 1 < ℓ),
        T.metaTree.Adj (order i) (order ⟨i.1 + 1, hi⟩)

end Lax17.TreeOfSets
end
