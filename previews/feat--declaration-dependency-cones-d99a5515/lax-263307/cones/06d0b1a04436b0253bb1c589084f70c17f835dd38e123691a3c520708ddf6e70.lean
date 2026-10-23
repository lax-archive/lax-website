-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Floor

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance

namespace Lax263307.WeightedIndependentSet

/-- Total weight of a vertex set. -/
def weight {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : ℚ :=
  ∑ v ∈ I, w v

/-- An independent set that achieves the requested multiplicative guarantee. -/
def IsApproximation {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (I : Finset (Fin n)) : Prop :=
  G.IsIndepSet (I : Set (Fin n)) ∧
    ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) →
      (1 - ε) * weight w J ≤ weight w I

end Lax263307.WeightedIndependentSet
end

-- Lax263307.PositiveWeights
section
namespace Lax263307.PositiveWeights

open WeightedIndependentSet

/-- Clip negative weights to zero. -/
def positiveWeights {n : ℕ} (w : Fin n → ℚ) : Fin n → ℚ := fun v => max (w v) 0

/-- Retain only the strictly positive-weight vertices of a returned set. -/
def discardNonpositive {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : Finset (Fin n) :=
  I.filter fun v => 0 < w v

/-- Approximation for clipped weights transfers to arbitrary signed weights. -/
axiom signed_weight_transfer {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (accuracy_nonnegative : 0 ≤ ε) (accuracy_le_one : ε ≤ 1)
    (I : Finset (Fin n)) (approximation : IsApproximation G (positiveWeights w) ε I) :
    IsApproximation G w ε (discardNonpositive w I)

end Lax263307.PositiveWeights
end
