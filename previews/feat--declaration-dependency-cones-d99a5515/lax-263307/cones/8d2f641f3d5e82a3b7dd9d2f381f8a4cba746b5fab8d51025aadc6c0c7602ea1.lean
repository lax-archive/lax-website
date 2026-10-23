-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Lattice

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

end Lax228581.Treewidth
end

-- Lax263307.ConnectedBags
section
namespace Lax263307.ConnectedBags

open Lax228581.Treewidth

/-- The decomposition nodes whose bags meet `U`. -/
def meetingNodes {n : ℕ} {G : SimpleGraph (Fin n)}
    (D : TreeDecomposition G) (U : Finset (Fin n)) : Set D.Node :=
  {i | ∃ v ∈ U, v ∈ D.bag i}

/-- Connected vertex sets meet a connected collection of decomposition bags. -/
axiom meeting_connected {n : ℕ} (G : SimpleGraph (Fin n))
    (D : TreeDecomposition G) (U : Finset (Fin n))
    (connected : (G.induce (↑U : Set (Fin n))).Connected) :
    (D.tree.induce (meetingNodes D U)).Connected

end Lax263307.ConnectedBags
end
