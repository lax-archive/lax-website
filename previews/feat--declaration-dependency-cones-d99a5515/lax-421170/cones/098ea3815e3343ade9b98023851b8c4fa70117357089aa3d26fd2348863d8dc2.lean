-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Lattice.Nat

-- Lax421170.AnnihilationNumber
section
namespace Lax421170.AnnihilationNumber

/-- The degrees of the vertices of `G`, listed in nondecreasing order. -/
def degreeSequence {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    List ℕ :=
  (Finset.univ.val.map fun v => G.degree v).sort (· ≤ ·)

end Lax421170.AnnihilationNumber
end
