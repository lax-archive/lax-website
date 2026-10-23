-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Log

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

-- Lax17.Treewidth
section
namespace Lax17.Treewidth

universe u

/-- A finite tree decomposition of a simple graph. -/
structure TreeDecomposition {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) where
  /-- The node type of the decomposition tree. -/
  Node : Type
  /-- The decomposition tree has finitely many nodes. -/
  [nodeFintype : Fintype Node]
  /-- Decomposition-tree nodes have decidable equality. -/
  [nodeDecidableEq : DecidableEq Node]
  /-- The tree on decomposition nodes. -/
  tree : SimpleGraph Node
  /-- The node graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag assigned to each decomposition node. -/
  bag : Node → Finset V
  /-- Every graph vertex occurs in a bag. -/
  vertex_mem_bag : ∀ v : V, ∃ i : Node, v ∈ bag i
  /-- The endpoints of every graph edge occur together in a bag. -/
  edge_mem_bag :
    ∀ ⦃x y : V⦄, G.Adj x y → ∃ i : Node, x ∈ bag i ∧ y ∈ bag i
  /-- Bags containing a fixed graph vertex induce a connected subtree. -/
  bag_indices_connected :
    ∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected

namespace TreeDecomposition

/-- The maximum bag cardinality minus one. -/
noncomputable def width {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} (D : TreeDecomposition G) : ℕ :=
  letI : Fintype D.Node := D.nodeFintype
  (Finset.univ.sup fun i : D.Node => (D.bag i).card) - 1

end TreeDecomposition

/-- `G` has a tree decomposition of width at most `k`. -/
def HasTreewidthAtMost {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : TreeDecomposition G, D.width ≤ k

/-- The least width of a tree decomposition of `G`.

The fallback makes the definition total. For a finite graph it is unreachable,
because the decomposition with one bag containing every vertex always exists.
-/
noncomputable def treewidth {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  letI := Classical.decPred (HasTreewidthAtMost G)
  letI := Classical.propDecidable (∃ k, HasTreewidthAtMost G k)
  if h : ∃ k, HasTreewidthAtMost G k then Nat.find h else 0

end Lax17.Treewidth
end

-- Lax17.StrongPathOfSetsFromTreewidth
section
namespace Lax17.StrongPathOfSetsFromTreewidth

universe u

/-- Sufficiently large treewidth produces a strong path-of-sets system of
prescribed length and width. -/
axiom strongPathOfSetsFromTreewidth :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {ℓ w k : ℕ},
        1 < ℓ →
          1 < w →
            1 < k →
              k ≤ Lax17.Treewidth.treewidth G →
                c * w * ℓ ^ 50 * (Nat.log 2 k) ^ d < k →
                  Nonempty (Lax17.PathOfSets.StrongSystem G ℓ w)

end Lax17.StrongPathOfSetsFromTreewidth
end
