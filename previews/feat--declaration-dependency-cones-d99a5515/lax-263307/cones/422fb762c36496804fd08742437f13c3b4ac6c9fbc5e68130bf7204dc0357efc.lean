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
namespace Lax263307
end Lax263307

namespace Lax263307.ConnectedBags
end Lax263307.ConnectedBags
end

-- Lax263307.ConnectedRepresentations
section
namespace Lax263307.ConnectedRepresentations

open Lax228581.Treewidth

/-- A connected vertex set in `G` for each vertex of `H`. -/
structure Representation {t n : ℕ} (H : SimpleGraph (Fin t))
    (G : SimpleGraph (Fin n)) where
  /-- The vertices used by a represented vertex. -/
  carrier : Fin t → Finset (Fin n)
  /-- Each carrier is nonempty and connected. -/
  connected : ∀ v, (G.induce (↑(carrier v) : Set (Fin n))).Connected
  /-- Carriers of adjacent vertices intersect. -/
  touching : ∀ u v, H.Adj u v → ∃ a, a ∈ carrier u ∧ a ∈ carrier v

/-- Which represented vertices use a particular host vertex. -/
def users {t n : ℕ} {H : SimpleGraph (Fin t)} {G : SimpleGraph (Fin n)}
    (R : Representation H G) (a : Fin n) : Finset (Fin t) :=
  Finset.univ.filter fun v => a ∈ R.carrier v

/-- Transfer a decomposition with a uniform bound on the representation load. -/
axiom transfer_decomposition {t n : ℕ} (H : SimpleGraph (Fin t))
    (G : SimpleGraph (Fin n)) (R : Representation H G)
    (B w : ℕ) (load_bound : ∀ a, (users R a).card ≤ B)
    (D : TreeDecomposition G) (bag_bound : ∀ i, (D.bag i).card ≤ w) :
    ∃ D' : TreeDecomposition H, ∀ i, (D'.bag i).card ≤ B * w

end Lax263307.ConnectedRepresentations
end
