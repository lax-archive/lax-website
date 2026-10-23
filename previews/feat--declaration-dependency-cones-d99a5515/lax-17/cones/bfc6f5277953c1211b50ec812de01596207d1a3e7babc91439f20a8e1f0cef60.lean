-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
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

-- Lax17.TreewidthSparsifier
section
namespace Lax17.TreewidthSparsifier

universe u

/-- If `G` has treewidth at least `k > 1`, it has a spanning subgraph `H` of
maximum degree three for which
`k ≤ c · treewidth(H) · (log₂ k)^d`. -/
axiom degreeThreeTreewidthSparsifier :
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) {k : ℕ},
        1 < k →
          k ≤ Lax17.Treewidth.treewidth G →
            ∃ H : SimpleGraph V,
              H ≤ G ∧
                Lax17.Degree.MaximumAtMost H 3 ∧
                  k ≤ c * Lax17.Treewidth.treewidth H *
                    (Nat.log 2 k) ^ d

end Lax17.TreewidthSparsifier
end
