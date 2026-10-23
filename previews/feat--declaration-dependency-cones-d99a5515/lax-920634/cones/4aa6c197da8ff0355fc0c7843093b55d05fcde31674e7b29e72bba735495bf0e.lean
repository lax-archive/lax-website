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

/-- Replace each base vertex by a path of its ports and add the paired-port edges. -/
def graph {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d) :
    SimpleGraph (Fin n × Fin d) :=
  SimpleGraph.fromRel (fun u v =>
    (u.1 = v.1 ∧ u.2.val + 1 = v.2.val) ∨ v = R u)

end Lax920634.PathReplacement
end
