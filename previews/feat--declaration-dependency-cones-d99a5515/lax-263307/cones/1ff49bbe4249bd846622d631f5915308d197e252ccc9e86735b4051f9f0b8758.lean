-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic
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

end Lax228581.Treewidth
end

-- Lax263307.GraphClasses
section
namespace Lax263307.GraphClasses

/-- A class of finite simple graphs, represented on numbered vertex sets. -/
abbrev GraphClass := (n : ℕ) → Set (SimpleGraph (Fin n))

/-- Every graph that embeds as an induced subgraph of a member also belongs. -/
def IsHereditary (C : GraphClass) : Prop :=
  ∀ (m n : ℕ) (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)),
    G ∈ C n → Nonempty (H ↪g G) → H ∈ C m

end Lax263307.GraphClasses
end

-- Lax263307.EdgeSublinearSeparators
section
namespace Lax263307.EdgeSublinearSeparators

open GraphClasses

/-- Each component after deleting `S` contains at most two thirds of the vertices. -/
def IsBalancedSeparator {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Prop :=
  ∀ K : (G.induce (↑S : Set (Fin n))ᶜ).ConnectedComponent,
    3 * K.supp.ncard ≤ 2 * n

end Lax263307.EdgeSublinearSeparators
end

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance

namespace Lax263307.WeightedIndependentSet

/-- Total weight of a vertex set. -/
def weight {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : ℚ :=
  ∑ v ∈ I, w v

/-- An independent set that achieves the requested multiplicative guarantee. -/
def IsApproximation {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (I : Finset (Fin n)) : Prop :=
  G.IsIndepSet (I : Set (Fin n)) ∧
    ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) →
      (1 - ε) * weight w J ≤ weight w I

end Lax263307.WeightedIndependentSet
end

-- Lax263307.RecursionDepth
section
namespace Lax263307.RecursionDepth

open WeightedIndependentSet (IsApproximation)

/-- Number of balanced reductions needed to reach order at most one. -/
def depth (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else 1 + depth (2 * n / 3)
termination_by n
decreasing_by omega

end Lax263307.RecursionDepth
end

-- Lax263307.LinearRelaxation
section
namespace Lax263307
end Lax263307

namespace Lax263307.LinearRelaxation
end Lax263307.LinearRelaxation

namespace Lax263307.LinearRelaxation.IsFeasible
end Lax263307.LinearRelaxation.IsFeasible
end

-- Lax263307.SeparatorComponents
section
namespace Lax263307.SeparatorComponents
end Lax263307.SeparatorComponents

namespace Lax263307.SeparatorComponents.Partition
end Lax263307.SeparatorComponents.Partition
end

-- Lax263307.SeparatorDecompositions
section
namespace Lax263307.SeparatorDecompositions

open RecursionDepth (depth)

open GraphClasses EdgeSublinearSeparators SeparatorComponents Lax228581.Treewidth

/-- Balanced recursive separators give a logarithmic depth bag bound. -/
axiom recursive_bag_bound (C : GraphClass) (hereditary : IsHereditary C)
    (B : ℕ → ℕ) (monotone : Monotone B) (positive : ∀ m, 1 ≤ B m)
    (separators : ∀ n (G : SimpleGraph (Fin n)), G ∈ C n →
      ∃ S : Finset (Fin n), IsBalancedSeparator G S ∧ S.card ≤ B G.edgeSet.ncard)
    {n : ℕ} (G : SimpleGraph (Fin n)) (member : G ∈ C n) :
    ∃ D : TreeDecomposition G, ∀ j,
      (D.bag j).card ≤ B G.edgeSet.ncard * (depth n + 1)

end Lax263307.SeparatorDecompositions
end
