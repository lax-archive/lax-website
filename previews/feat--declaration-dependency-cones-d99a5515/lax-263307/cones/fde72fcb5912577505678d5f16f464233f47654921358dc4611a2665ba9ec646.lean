-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Floor

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307.WeightedIndependentSet

/-- A finite graph with rational vertex weights. -/
structure Instance where
  order : ℕ
  graph : SimpleGraph (Fin order)
  weights : Fin order → ℚ

end Lax263307.WeightedIndependentSet
end
