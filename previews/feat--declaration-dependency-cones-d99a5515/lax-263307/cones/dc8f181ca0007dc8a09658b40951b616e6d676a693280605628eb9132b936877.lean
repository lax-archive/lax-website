-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
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
namespace Lax263307
end Lax263307

namespace Lax263307.ConnectedBags
end Lax263307.ConnectedBags
end

-- Lax263307.ConnectedRepresentations
section
namespace Lax263307.ConnectedRepresentations
end Lax263307.ConnectedRepresentations

namespace Lax263307.ConnectedRepresentations.Representation
end Lax263307.ConnectedRepresentations.Representation
end

-- Lax263307.AlmostEmbeddings
section
namespace Lax263307.AlmostEmbeddings

open scoped Classical

open Lax228581.Treewidth

/-- A connected route for every edge, disjoint for nonincident edges. -/
structure AlmostEmbedding {t n : ℕ} (H : SimpleGraph (Fin t))
    (G : SimpleGraph (Fin n)) where
  /-- Vertex images, with no injectivity requirement. -/
  vertexMap : Fin t → Fin n
  /-- Host vertices on each route. -/
  route : H.edgeSet → Finset (Fin n)
  /-- Each route is nonempty and connected. -/
  connected : ∀ e, (G.induce (↑(route e) : Set (Fin n))).Connected
  /-- A route contains the images of its edge's endpoints. -/
  endpoints : ∀ e v, v ∈ e.val → vertexMap v ∈ route e
  /-- Routes of nonincident edges share no host vertex. -/
  disjoint : ∀ e f, Disjoint e.val.toFinset f.val.toFinset → Disjoint (route e) (route f)

/-- An almost-embedding transfers decompositions with at most factor `2d` loss. -/
axiom transfer_decomposition {t n : ℕ} (H : SimpleGraph (Fin t))
    [DecidableRel H.Adj] (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G)
    (d w : ℕ) (degree_bound : ∀ v, H.degree v ≤ d)
    (no_isolates : ∀ v, ¬H.IsIsolated v)
    (D : TreeDecomposition G) (bag_bound : ∀ i, (D.bag i).card ≤ w) :
    ∃ D' : TreeDecomposition H, ∀ i, (D'.bag i).card ≤ 2 * d * w

end Lax263307.AlmostEmbeddings
end
