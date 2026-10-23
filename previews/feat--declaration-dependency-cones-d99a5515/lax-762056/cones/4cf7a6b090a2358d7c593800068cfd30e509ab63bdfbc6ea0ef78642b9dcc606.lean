-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Paths

-- Lax762056.AsteroidalCycles
section
namespace Lax762056.AsteroidalCycles

open SimpleGraph

def AvoidsClosedNeighborhood {V : Type*} (G : SimpleGraph V)
    (S T : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ T, x ≠ y ∧ ¬ G.Adj x y

end Lax762056.AsteroidalCycles
end
