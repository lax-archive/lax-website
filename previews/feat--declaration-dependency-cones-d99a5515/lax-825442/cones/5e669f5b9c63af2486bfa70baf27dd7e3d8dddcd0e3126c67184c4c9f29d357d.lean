-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat

-- Lax825442.DistanceToClique
section
namespace Lax825442.DistanceToClique

/-- Minimum number of vertices whose deletion leaves a complete graph. -/
noncomputable def distanceToClique {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, (S.card = k) ∧
    (G.induce {v | v ∉ S} = ⊤)}

end Lax825442.DistanceToClique
end
