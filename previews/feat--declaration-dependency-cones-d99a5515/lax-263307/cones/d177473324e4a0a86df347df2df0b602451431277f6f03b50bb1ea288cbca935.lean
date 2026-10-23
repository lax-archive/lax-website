-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Floor

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307
end Lax263307

namespace Lax263307.WeightedIndependentSet
end Lax263307.WeightedIndependentSet

namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance
end

-- Lax263307.PositiveWeights
section
namespace Lax263307.PositiveWeights

open WeightedIndependentSet

/-- Retain only the strictly positive-weight vertices of a returned set. -/
def discardNonpositive {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : Finset (Fin n) :=
  I.filter fun v => 0 < w v

end Lax263307.PositiveWeights
end
