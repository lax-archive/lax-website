-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

-- Lax825442.NeighborhoodDiversity
section
namespace Lax825442.NeighborhoodDiversity

/-- A partition into `k` parts, each a module and each inducing a clique or
an independent set. Empty labels are allowed and disappear at the minimum. -/
def HasNeighborhoodDiversityAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ part : V → Fin k,
    (∀ u v w : V,
      (part u = part v ∧ part w ≠ part u) → (G.Adj u w ↔ G.Adj v w)) ∧
    (∀ i : Fin k,
      (∀ u v : V,
        (u ≠ v ∧ (part u = i ∧ part v = i)) → G.Adj u v) ∨
      (∀ u v : V,
        (part u = i ∧ part v = i) → ¬ G.Adj u v))

end Lax825442.NeighborhoodDiversity
end
