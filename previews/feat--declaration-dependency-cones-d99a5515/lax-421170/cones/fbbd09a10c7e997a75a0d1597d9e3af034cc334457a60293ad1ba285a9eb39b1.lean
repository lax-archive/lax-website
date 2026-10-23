-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
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

/-- The largest `k ≤ n` such that the first `k` entries of the nondecreasing degree
sequence, i.e. the `k` smallest degrees, sum to at most the number of edges. -/
noncomputable def annihilationNumber {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  sSup {k : ℕ | k ≤ Fintype.card V ∧ ((degreeSequence G).take k).sum ≤ G.edgeFinset.card}

end Lax421170.AnnihilationNumber
end

-- Lax421170.IndependenceBound
section
namespace Lax421170.IndependenceBound

open Lax421170.AnnihilationNumber

/-- The independence number of a finite simple graph is at most its annihilation number. -/
axiom indepNum_le_annihilationNumber {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : G.indepNum ≤ annihilationNumber G

end Lax421170.IndependenceBound
end
