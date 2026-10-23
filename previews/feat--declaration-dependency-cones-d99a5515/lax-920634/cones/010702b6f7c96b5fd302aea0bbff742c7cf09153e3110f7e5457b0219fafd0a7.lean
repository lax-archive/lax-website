-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card

-- Lax920634.EdgeExpansion
section
namespace Lax920634
end Lax920634

namespace Lax920634.EdgeExpansion
end Lax920634.EdgeExpansion
end

-- Lax920634.PathReplacement
section
namespace Lax920634.PathReplacement

/-- Base boundary darts with source in `S` and target outside `S`. -/
def baseCut {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (S : Set (Fin n)) : Set (Fin n × Fin d) :=
  {p | p.1 ∈ S ∧ (R p).1 ∉ S}

end Lax920634.PathReplacement
end
