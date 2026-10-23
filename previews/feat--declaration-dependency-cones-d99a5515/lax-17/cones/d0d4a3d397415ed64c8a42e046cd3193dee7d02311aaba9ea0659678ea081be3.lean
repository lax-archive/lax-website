-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

/-- The finite set of edges used by a path. -/
noncomputable def edges {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) : Finset (Sym2 V) :=
  P.walk.edges.toFinset

/-- `P` is oriented from `A` to `B`. -/
def Connects {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (A B : Finset V) : Prop :=
  P.source ∈ A ∧ P.target ∈ B

/-- Every vertex of `P` lies in `C`. -/
def StaysIn {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (P : Path G) (C : Finset V) : Prop :=
  P.vertices ⊆ C

end Path

/-- Exactly `k` pairwise vertex-disjoint paths oriented from `A` to `B`. -/
structure VertexLinkage {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ) where
  path : Fin k → Path G
  connects : ∀ i : Fin k, (path i).Connects A B
  vertex_disjoint :
    Pairwise fun i j => Disjoint (path i).vertices (path j).vertices

/-- Exactly `k` pairwise edge-disjoint paths oriented from `A` to `B`. -/
structure EdgeLinkage {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ) where
  path : Fin k → Path G
  connects : ∀ i : Fin k, (path i).Connects A B
  edge_disjoint :
    Pairwise fun i j => Disjoint (path i).edges (path j).edges

end Lax17.Paths
end

-- Lax17.Linkedness
section
namespace Lax17.Linkedness

universe u

open Lax17.Paths

/-- `X` is node-well-linked inside `C`. -/
def NodeWellLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C X : Finset V) : Prop :=
  X ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ X → B ⊆ X → Disjoint A B →
      ∃ P : VertexLinkage G A B (min A.card B.card),
        ∀ i : Fin (min A.card B.card), (P.path i).StaysIn C

/-- `X` is edge-well-linked inside `C`. -/
def EdgeWellLinkedIn {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (C X : Finset V) : Prop :=
  X ⊆ C ∧
    ∀ ⦃A B : Finset V⦄, A ⊆ X → B ⊆ X → Disjoint A B →
      ∃ P : EdgeLinkage G A B (min A.card B.card),
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

-- Lax17.WellLinkednessBoosting
section
namespace Lax17.WellLinkednessBoosting

universe u

/-- In a connected cluster of a graph of maximum degree `Δ ≥ 3`, an
edge-well-linked terminal set of size `κ` contains a node-well-linked subset
of size at least `⌊κ / (4Δ)⌋`. -/
axiom wellLinkednessBoosting :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C T : Finset V) (Δ κ : ℕ),
      Lax17.PathOfSets.IsCluster G C →
        Lax17.Degree.MaximumAtMost G Δ →
          3 ≤ Δ →
            T.card = κ →
              Lax17.Linkedness.EdgeWellLinkedIn G C T →
                ∃ T' : Finset V,
                  T' ⊆ T ∧ κ / (4 * Δ) ≤ T'.card ∧
                    Lax17.Linkedness.NodeWellLinkedIn G C T'

end Lax17.WellLinkednessBoosting
end
