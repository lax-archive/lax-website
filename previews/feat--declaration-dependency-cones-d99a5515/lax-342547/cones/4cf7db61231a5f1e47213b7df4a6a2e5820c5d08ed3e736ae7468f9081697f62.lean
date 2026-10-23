-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

-- Lax342547.PeelingBudget
section
namespace Lax342547.PeelingBudget

open scoped ENNReal

axiom rank_comparison (D ζ ε : ℝ) (N u : ℕ) (hN : 0 < N) (m : ℝ≥0∞)
    (hlower : (2 : ℝ≥0∞) ^ (-(ζ * N)) * ((2 : ℝ≥0∞) ^ (-((1 - ζ) * N))) ^ u < m)
    (hupper : m ≤ (2 : ℝ≥0∞) ^ (D * N) * ((2 : ℝ≥0∞) ^ (-((1 - ε) * N))) ^ u) :
    (ζ - ε) * u < D + ζ

end Lax342547.PeelingBudget
end
