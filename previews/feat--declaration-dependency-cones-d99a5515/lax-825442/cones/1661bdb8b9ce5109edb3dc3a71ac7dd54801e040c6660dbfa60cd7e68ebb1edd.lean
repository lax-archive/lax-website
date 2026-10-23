-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat

-- Lax825442.Degeneracy
section
namespace Lax825442.Degeneracy

/-- Every nonempty induced subgraph has a vertex of degree at most `k`. -/
def HasDegeneracyAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty →
    (∃ v : V, v ∈ S ∧
      ({u : V | u ∈ S ∧ G.Adj v u}.ncard ≤ k))

end Lax825442.Degeneracy
end
