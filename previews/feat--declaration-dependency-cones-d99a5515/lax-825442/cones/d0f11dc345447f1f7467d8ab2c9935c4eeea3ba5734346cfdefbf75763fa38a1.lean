-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

-- Lax825442.MaximumMatching
section
namespace Lax825442.MaximumMatching

/-- The maximum number of edges in a matching. -/
noncomputable def maximumMatching {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sSup {n : ℕ | ∃ M : G.Subgraph, M.IsMatching ∧ (M.edgeSet.ncard = n)}

end Lax825442.MaximumMatching
end
