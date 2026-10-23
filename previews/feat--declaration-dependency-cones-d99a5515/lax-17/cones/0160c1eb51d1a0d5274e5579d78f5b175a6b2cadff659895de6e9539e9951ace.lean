-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Log

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

/-- Edges of `G` with one endpoint in `X` and the other in `Y`. -/
noncomputable def edgeBoundary {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X Y : Finset V) : Finset (Sym2 V) :=
  @Finset.filter (Sym2 V)
    (fun e => e ∈ G.edgeSet ∧ ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y))
    (Classical.decPred fun e =>
      e ∈ G.edgeSet ∧ ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y))
    Finset.univ

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

/-- Cut-based edge well-linkedness with parameter `numerator / denominator`.
Every partition of the whole vertex set cuts the corresponding fraction of
the smaller terminal side. -/
def ScaledEdgeWellLinked {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V)
    (numerator denominator : ℕ) : Prop :=
  0 < numerator ∧ numerator ≤ denominator ∧
    ∀ X Y : Finset V,
      X ∪ Y = Finset.univ → Disjoint X Y →
        numerator * min (X ∩ T).card (Y ∩ T).card ≤
          denominator * (edgeBoundary G X Y).card

end Lax17.Linkedness
end

-- Lax17.PathOfSets
section
namespace Lax17.PathOfSets.HairyClusterSplit
end Lax17.PathOfSets.HairyClusterSplit

namespace Lax17.PathOfSets.HairySystem
end Lax17.PathOfSets.HairySystem

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

/-- A path-of-sets system of length `ℓ` and width `w`. -/
structure System {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (ℓ w : ℕ) where
  length_pos : 0 < ℓ
  width_pos : 0 < w
  cluster : Fin ℓ → Finset V
  cluster_connected : ∀ i : Fin ℓ, IsCluster G (cluster i)
  cluster_disjoint :
    ∀ ⦃i j : Fin ℓ⦄, i ≠ j → Disjoint (cluster i) (cluster j)
  left : Fin ℓ → Finset V
  right : Fin ℓ → Finset V
  left_subset : ∀ i : Fin ℓ, left i ⊆ cluster i
  right_subset : ∀ i : Fin ℓ, right i ⊆ cluster i
  interfaces_disjoint : ∀ i : Fin ℓ, Disjoint (left i) (right i)
  left_card : ∀ i : Fin ℓ, (left i).card = w
  right_card : ∀ i : Fin ℓ, (right i).card = w
  connector :
    (i : Fin ℓ) → (hi : i.1 + 1 < ℓ) →
      VertexLinkage G (right i) (left ⟨i.1 + 1, hi⟩) w
  connector_avoids_clusters :
    ∀ (i : Fin ℓ) (hi : i.1 + 1 < ℓ) (j : Fin ℓ)
      (a : Fin w),
        (connector i hi).path a |>.InternallyAvoids (cluster j)
  connectors_disjoint :
    ∀ ⦃i j : Fin ℓ⦄ (hi : i.1 + 1 < ℓ) (hj : j.1 + 1 < ℓ),
      i ≠ j → ∀ a b : Fin w,
        Disjoint ((connector i hi).path a).vertices
          ((connector j hj).path b).vertices

namespace System

end System

/-- A strong path-of-sets system. -/
structure StrongSystem {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (ℓ w : ℕ) extends System G ℓ w where
  left_well_linked :
    ∀ i : Fin ℓ, NodeWellLinkedIn G (cluster i) (left i)
  right_well_linked :
    ∀ i : Fin ℓ, NodeWellLinkedIn G (cluster i) (right i)
  interfaces_linked :
    ∀ i : Fin ℓ, NodeLinkedIn G (cluster i) (left i) (right i)

end Lax17.PathOfSets
end

-- Lax17.LowDegreeWellLinkedCore
section
namespace Lax17.LowDegreeWellLinkedCore

universe u

/-- The local strong-path form of the degree-three sparsifier theorem. -/
axiom lowDegreeWellLinkedCore :
  ∃ cLength logLength cWellLinked logWellLinked : ℕ,
    0 < cLength ∧ 0 < logLength ∧
      0 < cWellLinked ∧ 0 < logWellLinked ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} {length width : ℕ}
      (P : Lax17.PathOfSets.StrongSystem G length width),
        1 < width →
          (∃ half : ℕ, width = 2 * half) →
            cLength * (Nat.log 2 width) ^ logLength ≤ length →
              ∃ H : SimpleGraph V,
                H ≤ G ∧
                  Lax17.Degree.MaximumAtMost H 3 ∧
                    Lax17.Linkedness.ScaledEdgeWellLinked H
                      (P.left ⟨0, P.length_pos⟩) 1
                        (cWellLinked *
                          (Nat.log 2 width) ^ logWellLinked)

end Lax17.LowDegreeWellLinkedCore
end
