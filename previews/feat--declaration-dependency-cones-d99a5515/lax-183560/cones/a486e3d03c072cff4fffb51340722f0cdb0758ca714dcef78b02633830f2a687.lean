-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

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
