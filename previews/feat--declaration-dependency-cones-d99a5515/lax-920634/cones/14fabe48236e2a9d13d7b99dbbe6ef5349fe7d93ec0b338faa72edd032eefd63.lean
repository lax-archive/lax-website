-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card

-- Lax228581.Treewidth
section
namespace Lax228581.Treewidth

/-- A tree decomposition of a simple graph: a finite tree of nodes with a bag
of graph vertices at each node, such that the bags cover every vertex and
every edge, and the nodes whose bags contain any fixed vertex induce a
connected subgraph of the tree. -/
structure TreeDecomposition {V : Type} (G : SimpleGraph V) where
  /-- The node type of the decomposition tree. -/
  Node : Type
  /-- The decomposition tree is finite. -/
  [nodeFintype : Fintype Node]
  /-- The graph on the decomposition nodes. -/
  tree : SimpleGraph Node
  /-- The node graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag assigned to each decomposition node. -/
  bag : Node → Finset V
  /-- Every graph vertex appears in at least one bag. -/
  vertex_mem_bag : ∀ v : V, ∃ i : Node, v ∈ bag i
  /-- Every graph edge has both endpoints together in at least one bag. -/
  edge_mem_bag : ∀ ⦃u v : V⦄, G.Adj u v → ∃ i : Node, u ∈ bag i ∧ v ∈ bag i
  /-- For each graph vertex, the nodes whose bags contain it induce a
  connected subgraph of the tree. -/
  bag_indices_connected :
    ∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected

/-- `G` has a tree decomposition all of whose bags have at most `w + 1`
vertices. -/
def HasTreewidthAtMost {V : Type} (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ D : TreeDecomposition G, ∀ i, (D.bag i).card ≤ w + 1

/-- The treewidth of a finite simple graph: the least `w` such that the
graph has a tree decomposition with bags of at most `w + 1` vertices. -/
noncomputable def treewidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {w | HasTreewidthAtMost G w}

end Lax228581.Treewidth
end

-- Lax920634.EdgeExpansion
section
namespace Lax920634.EdgeExpansion

/-- Boundary edges oriented from the set to its complement, each counted once. -/
def edgeBoundary {V : Type} (G : SimpleGraph V) (S : Set V) : Set (V × V) :=
  {e | e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2}

/-- Every vertex set of size at most half the graph has at least `h` times
its size in boundary edges. -/
def HasEdgeExpansionAtLeast {V : Type} [Fintype V]
    (G : SimpleGraph V) (h : ℚ) : Prop :=
  ∀ S : Set V, 2 * S.ncard ≤ Fintype.card V →
    h * (S.ncard : ℚ) ≤ ((edgeBoundary G S).ncard : ℚ)

/-- Every vertex has at most three distinct neighbors. -/
def IsSubcubic {V : Type} [Finite V] (G : SimpleGraph V) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ 3

end Lax920634.EdgeExpansion
end

-- Lax920634.ExpansionTreewidth
section
namespace Lax920634.ExpansionTreewidth

open EdgeExpansion Lax228581.Treewidth

/-- Uniform expansion in a subcubic graph gives a linear lower bound on treewidth. -/
axiom order_le_treewidth {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) (hd : 0 < d)
    (hdegree : IsSubcubic G)
    (hex : HasEdgeExpansionAtLeast G (1 / (8 * (d : ℚ)))) :
  n ≤ (24 * d + 1) * (treewidth G + 1)

end Lax920634.ExpansionTreewidth
end
