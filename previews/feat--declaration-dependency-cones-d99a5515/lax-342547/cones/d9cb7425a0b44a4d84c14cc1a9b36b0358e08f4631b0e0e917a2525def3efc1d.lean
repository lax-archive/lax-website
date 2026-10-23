-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

-- Lax342547.PeelingBudget
section
namespace Lax342547.PeelingBudget

open scoped ENNReal

axiom density_cost (D ζ : ℝ) (N u K : ℕ) (hζ : 0 ≤ ζ) (hζ₁ : ζ ≤ 1)
    (hu : u ≤ K) (m : ℝ≥0∞)
    (hm : (2 : ℝ≥0∞) ^ (-(ζ * N)) * ((2 : ℝ≥0∞) ^ (-((1 - ζ) * N))) ^ u ≤ m) :
    (2 : ℝ≥0∞) ^ (D * N) / m ≤ (2 : ℝ≥0∞) ^ ((D + K + 1) * N)

end Lax342547.PeelingBudget
end
