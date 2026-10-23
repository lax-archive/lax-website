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

/-- The empty set solves instances whose weights are all nonpositive. -/
axiom nonpositive_case {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (nonpositive : ∀ v, w v ≤ 0) (ε : ℚ) (accuracy_nonnegative : 0 ≤ ε)
    (accuracy_le_one : ε ≤ 1) : IsApproximation G w ε ∅

end Lax263307.PositiveWeights
end
