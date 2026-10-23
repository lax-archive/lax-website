-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Floor

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

end Lax228581.Treewidth
end

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307
end Lax263307

namespace Lax263307.WeightedIndependentSet
end Lax263307.WeightedIndependentSet

namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance
end

-- Lax263307.IndependentBlowUp
section
namespace Lax263307.IndependentBlowUp

/-- The vertices of an independent blow-up, including possibly empty fibres. -/
abbrev Vertex {n : ℕ} (copies : Fin n → ℕ) := (v : Fin n) × Fin (copies v)

/-- Copies are adjacent precisely when their original vertices are adjacent. -/
def graph {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ) :
    SimpleGraph (Vertex copies) := G.comap fun v => v.1

end Lax263307.IndependentBlowUp
end

-- Lax263307.BlowUpIndependentSets
section
namespace Lax263307.BlowUpIndependentSets
end Lax263307.BlowUpIndependentSets
end

-- Lax263307.BlowUpDecompositions
section
namespace Lax263307.BlowUpDecompositions
end Lax263307.BlowUpDecompositions
end

-- Lax263307.BlowUpDeletion
section
namespace Lax263307.BlowUpDeletion

open scoped Classical

open IndependentBlowUp Lax228581.Treewidth

/-- The vertices removed at degree threshold `s`. -/
noncomputable def highDegree {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (s : ℕ) : Finset (Vertex copies) :=
  Finset.univ.filter fun v => s < (graph G copies).degree v

/-- Lift bounded fibres, add singleton bags, and restore the deleted set. -/
axiom deletion_decomposition {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (s w : ℕ) (width : HasTreewidthAtMost G w) :
    ∃ D : TreeDecomposition (graph G copies),
      ∀ i, (D.bag i).card ≤ (highDegree G copies s).card + max 1 (s * (w + 1))

end Lax263307.BlowUpDeletion
end
