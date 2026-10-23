-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice
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

-- Lax379983.FeedbackVertexNumber
section
namespace Lax379983.FeedbackVertexNumber

/-- The minimum number of vertices whose deletion makes the graph acyclic. -/
noncomputable def feedbackVertexNumber {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ S : Set V, S.ncard = n ∧ (G.induce Sᶜ).IsAcyclic}

end Lax379983.FeedbackVertexNumber
end

-- Lax379983.TreewidthBound
section
namespace Lax379983.TreewidthBound

open Lax228581.Treewidth Lax379983.FeedbackVertexNumber

/-- Every finite simple graph has treewidth at most its feedback vertex number plus one. -/
axiom treewidth_le_feedbackVertexNumber_add_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : treewidth G ≤ feedbackVertexNumber G + 1

end Lax379983.TreewidthBound
end
