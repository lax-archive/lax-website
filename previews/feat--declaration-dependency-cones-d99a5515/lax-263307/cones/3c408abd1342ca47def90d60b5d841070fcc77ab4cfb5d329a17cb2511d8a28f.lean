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
namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance

namespace Lax263307.WeightedIndependentSet

/-- Total weight of a vertex set. -/
def weight {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : ℚ :=
  ∑ v ∈ I, w v

end Lax263307.WeightedIndependentSet
end

-- Lax263307.IndependentBlowUp
section
namespace Lax263307.IndependentBlowUp
end Lax263307.IndependentBlowUp
end

-- Lax263307.WeightRounding
section
namespace Lax263307.WeightRounding

/-- Multiplicities at a specified positive weight unit. -/
def roundedCopies {n : ℕ} (w : Fin n → ℚ) (τ : ℚ) : Fin n → ℕ :=
  fun v => ⌊w v / τ⌋₊

end Lax263307.WeightRounding
end

-- Lax263307.RoundingBounds
section
namespace Lax263307.RoundingBounds

open WeightedIndependentSet WeightRounding

/-- The additive rounding loss is at most the set cardinality times the scaling unit. -/
axiom set_rounding_loss {n : ℕ} (w : Fin n → ℚ) (τ : ℚ)
    (nonnegative : ∀ v, 0 ≤ w v) (positive_scale : 0 < τ) (J : Finset (Fin n)) :
    weight w J - (J.card : ℚ) * τ ≤ τ * ((∑ v ∈ J, roundedCopies w τ v : ℕ) : ℚ)

end Lax263307.RoundingBounds
end
