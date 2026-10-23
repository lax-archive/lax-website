-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

-- Lax342547.PeelingBudget
section
namespace Lax342547.PeelingBudget

open scoped ENNReal

axiom conservative_rank_bound (D ζ ε : ℝ) (u : ℕ)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : ε ≤ ζ / 4)
    (h : (ζ - ε) * u < D + ζ) : (u : ℝ) < 4 * (D + 1) / ζ

end Lax342547.PeelingBudget
end
