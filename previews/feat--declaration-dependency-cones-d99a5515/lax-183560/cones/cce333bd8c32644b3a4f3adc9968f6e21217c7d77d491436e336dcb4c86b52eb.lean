-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Lattice.Nat

-- Lax183560.BranchDecompositions
section
namespace Lax183560
end Lax183560

namespace Lax183560.BranchDecompositions
end Lax183560.BranchDecompositions

namespace Lax183560.BranchDecompositions.BinaryTree
end Lax183560.BranchDecompositions.BinaryTree

namespace Lax183560.BranchDecompositions.BinaryTree.fork
end Lax183560.BranchDecompositions.BinaryTree.fork

namespace Lax183560.BranchDecompositions.BinaryTree.leaf
end Lax183560.BranchDecompositions.BinaryTree.leaf

namespace Lax183560.BranchDecompositions.BinaryTree.leaves
end Lax183560.BranchDecompositions.BinaryTree.leaves
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

end Lax183560.Branchwidth
end
