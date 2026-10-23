-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card

-- Lax920634.EdgeExpansion
section
namespace Lax920634.EdgeExpansion

/-- Every vertex has at most three distinct neighbors. -/
def IsSubcubic {V : Type} [Finite V] (G : SimpleGraph V) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ 3

end Lax920634.EdgeExpansion
end
