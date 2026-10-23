-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax48.Treewidth
section
namespace Lax48.Treewidth

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

end Lax48.Treewidth
end

-- Lax48.TwinWidth
section
namespace Lax48.TwinWidth

/-- Two vertex sets are homogeneous in `G`: either every pair of vertices
across them is adjacent, or none is. -/
def Homogeneous {V : Type} (G : SimpleGraph V) (A B : Finset V) : Prop :=
  (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∨ (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)

/-- The red degree of a part `A` in a family of parts `P`: the number of
other parts of `P` that are not homogeneous with `A`. -/
noncomputable def redDegree {V : Type} (G : SimpleGraph V)
    (P : Finset (Finset V)) (A : Finset V) : ℕ :=
  {B | B ∈ P ∧ B ≠ A ∧ ¬ Homogeneous G A B}.ncard

/-- The partition of a finite vertex type into singletons. -/
def singletonPartition (V : Type) [Fintype V] [DecidableEq V] :
    Finset (Finset V) :=
  Finset.univ.image fun v : V => ({v} : Finset V)

/-- A partition sequence of `G` in which every part has red degree at most
`d`: starting from the singleton partition, each step merges two parts into
one, until a single part remains. -/
structure PartitionSequence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) where
  /-- The number of merge steps. -/
  stepCount : ℕ
  /-- The partition after each number of merge steps. -/
  partition : ℕ → Finset (Finset V)
  /-- The sequence starts at the singleton partition. -/
  starts : partition 0 = singletonPartition V
  /-- The sequence ends with a single part. -/
  ends : (partition stepCount).card ≤ 1
  /-- Each step merges two distinct parts into one and keeps all other
  parts. -/
  step_merges :
    ∀ i, i < stepCount → ∃ A ∈ partition i, ∃ B ∈ partition i, A ≠ B ∧
      partition (i + 1) = insert (A ∪ B) (((partition i).erase A).erase B)
  /-- Every part of every partition in the sequence has red degree at most
  `d`. -/
  redDegree_le :
    ∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ partition i →
      redDegree G (partition i) A ≤ d

/-- `G` has a partition sequence in which every part has red degree at most
`d`. -/
def HasTwinWidthAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  Nonempty (PartitionSequence G d)

/-- The twin-width of a finite simple graph: the least `d` such that the
graph has a partition sequence in which every part has red degree at most
`d`. -/
noncomputable def twinWidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {d | HasTwinWidthAtMost G d}

end Lax48.TwinWidth
end

-- Lax48.ExponentialSeparation
section
namespace Lax48.ExponentialSeparation

/-- For every `k`, some finite graph has treewidth at most `2 * k + 4` and
twin-width greater than `2 ^ k`. -/
axiom exists_treewidth_le_and_two_pow_lt_twinWidth (k : ℕ) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      Lax48.Treewidth.treewidth G ≤ 2 * k + 4 ∧
        2 ^ k < Lax48.TwinWidth.twinWidth G

end Lax48.ExponentialSeparation
end
