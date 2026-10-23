-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Sym

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

/-- The Appendix A.3 split of one cluster into a new base cluster and a
disjoint hair cluster, together with the retained interfaces and hair
linkage. -/
structure HairyClusterSplit {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C A B : Finset V) (w : ℕ) where
  baseCluster : Finset V
  hairCluster : Finset V
  left : Finset V
  right : Finset V
  baseEndpoint : Finset V
  hairEndpoint : Finset V
  base_subset : baseCluster ⊆ C
  hair_subset : hairCluster ⊆ C
  base_connected : IsCluster G baseCluster
  hair_connected : IsCluster G hairCluster
  clusters_disjoint : Disjoint baseCluster hairCluster
  left_subset_base : left ⊆ baseCluster
  right_subset_base : right ⊆ baseCluster
  baseEndpoint_subset : baseEndpoint ⊆ baseCluster
  hairEndpoint_subset : hairEndpoint ⊆ hairCluster
  left_subset_original : left ⊆ A
  right_subset_original : right ⊆ B
  left_card : left.card = w
  right_card : right.card = w
  baseEndpoint_card : baseEndpoint.card = w
  hairEndpoint_card : hairEndpoint.card = w
  interfaces_disjoint : Disjoint left right
  baseEndpoint_disjoint_interfaces :
    Disjoint baseEndpoint (left ∪ right)
  left_well_linked : NodeWellLinkedIn G baseCluster left
  right_well_linked : NodeWellLinkedIn G baseCluster right
  interfaces_linked : NodeLinkedIn G baseCluster left right
  left_baseEndpoint_linked :
    NodeLinkedIn G baseCluster left baseEndpoint
  hairEndpoint_well_linked :
    NodeWellLinkedIn G hairCluster hairEndpoint
  hairLinkage :
    VertexLinkage G baseEndpoint hairEndpoint w
  hairLinkage_stays_in_cluster :
    ∀ i : Fin w, (hairLinkage.path i).StaysIn C
  hairLinkage_avoids_base :
    ∀ i : Fin w, (hairLinkage.path i).InternallyAvoids baseCluster
  hairLinkage_avoids_hair :
    ∀ i : Fin w, (hairLinkage.path i).InternallyAvoids hairCluster

end Lax17.PathOfSets
end
