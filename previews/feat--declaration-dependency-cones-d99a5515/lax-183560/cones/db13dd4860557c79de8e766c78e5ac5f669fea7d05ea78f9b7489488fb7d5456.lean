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

end Lax183560.BranchDecompositions
end
