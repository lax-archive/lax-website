-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Lattice.Nat

-- Lax183560.BranchDecompositions
section
namespace Lax183560.BranchDecompositions

inductive BinaryTree (α : Type) where
  | leaf : α → BinaryTree α
  | fork : BinaryTree α → BinaryTree α → BinaryTree α

/-- Leaves with multiplicity, in left-to-right order. -/
def BinaryTree.leaves {α : Type} : BinaryTree α → List α
  | .leaf a => [a]
  | .fork left right => left.leaves ++ right.leaves

/-- A valid branch tree contains each element of the ground set once. -/
def BinaryTree.Valid {α : Type} [DecidableEq α]
    (t : BinaryTree α) (ground : Finset α) : Prop :=
  t.leaves.Nodup ∧ t.leaves.toFinset = ground

/-- Maximum cut value among the cuts at the nodes of a branch tree. -/
def BinaryTree.cutWidth {α : Type} [DecidableEq α]
    (measure : Finset α → ℕ) : BinaryTree α → ℕ
  | .leaf a => measure {a}
  | .fork left right =>
      max (measure ((left.leaves ++ right.leaves).toFinset))
        (max (left.cutWidth measure) (right.cutWidth measure))

end Lax183560.BranchDecompositions
end

-- Lax183560.Branchwidth
section
namespace Lax183560.Branchwidth

open Lax183560.BranchDecompositions

/-- Number of vertices incident with an edge in `A` and an edge outside `A`. -/
noncomputable def middleSize {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (Sym2 V)) : ℕ :=
  {v : V | (∃ e : Sym2 V, e ∈ G.edgeSet ∧ e ∈ A ∧ v ∈ e) ∧
    (∃ e : Sym2 V, e ∈ G.edgeSet ∧ e ∉ A ∧ v ∈ e)}.ncard

/-- A branch decomposition with every middle set of size at most `k`. -/
noncomputable def HasBranchwidthAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop := by
  classical
  exact G.edgeSet = ∅ ∨
    ∃ t : BranchDecompositions.BinaryTree (Sym2 V),
      t.Valid G.edgeFinset ∧
      t.cutWidth (middleSize G) ≤ k

end Lax183560.Branchwidth
end
