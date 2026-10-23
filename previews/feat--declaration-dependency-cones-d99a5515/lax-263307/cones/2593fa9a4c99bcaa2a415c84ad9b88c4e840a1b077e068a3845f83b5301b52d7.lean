-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
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

-- Lax263307.IndependentBlowUp
section
namespace Lax263307.IndependentBlowUp
end Lax263307.IndependentBlowUp
end

-- Lax263307.WeightRounding
section
namespace Lax263307.WeightRounding

/-- The maximum of the vertex weights and zero. -/
def maximumWeight {n : ℕ} (w : Fin n → ℚ) : ℚ :=
  (insert 0 (Finset.univ.image w)).max' (Finset.insert_nonempty _ _)

/-- The weight unit used by the reduction. -/
def scale {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : ℚ :=
  ε * maximumWeight w / (2 * n)

end Lax263307.WeightRounding
end
