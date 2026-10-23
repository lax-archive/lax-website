-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Log
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

-- Lax263307.RecursionDepth
section
namespace Lax263307.RecursionDepth.depth
end Lax263307.RecursionDepth.depth

namespace Lax263307.RecursionDepth

open WeightedIndependentSet (IsApproximation)

/-- A certified independence upper bound turns the accumulated loss into approximation. -/
axiom approximation_transfer {n : ℕ} (G : SimpleGraph (Fin n))
    (I : Finset (Fin n)) (u levels : ℕ) (δ ε : ℚ)
    (independent : G.IsIndepSet (I : Set (Fin n)))
    (upper_bound : ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card ≤ u)
    (δ_nonnegative : 0 ≤ δ) (δ_small : δ ≤ 1)
    (ε_small : ε ≤ 1) (loss : (levels : ℚ) * δ ≤ ε)
    (size : (1 - δ) ^ levels * (u : ℚ) ≤ I.card) :
    IsApproximation G (fun _ => 1) ε I

end Lax263307.RecursionDepth
end
