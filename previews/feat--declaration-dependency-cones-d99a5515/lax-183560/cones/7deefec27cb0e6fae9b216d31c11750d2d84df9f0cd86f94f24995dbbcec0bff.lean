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

-- Lax183560.CutRank
section
namespace Lax183560.CutRank

/-- Binary rank of the adjacency matrix across a cut. -/
noncomputable def cutRank {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) : ℕ := by
  classical
  let M : Matrix {v : V // v ∈ A} {v : V // v ∉ A} (ZMod 2) :=
    fun u v => if G.Adj u v then 1 else 0
  exact M.rank

end Lax183560.CutRank
end

-- Lax183560.Rankwidth
section
namespace Lax183560.Rankwidth

open Lax183560.BranchDecompositions Lax183560.CutRank

/-- Existence of a vertex branch decomposition of cut-rank at most `k`. -/
def HasRankwidthAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  IsEmpty V ∨
    ∃ t : BranchDecompositions.BinaryTree V,
      t.Valid Finset.univ ∧
      t.cutWidth (cutRank G) ≤ k

/-- The minimum maximum binary cut-rank. -/
noncomputable def rankwidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k | HasRankwidthAtMost G k}

end Lax183560.Rankwidth
end
