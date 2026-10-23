-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Real.Basic

-- Lax303562.PanopticQuality
section
namespace Lax303562
end Lax303562

namespace Lax303562.PanopticQuality
end Lax303562.PanopticQuality
end

-- Lax303562.WeightedFamily
section
namespace Lax303562.WeightedFamily

open Lax303562.PanopticQuality

/-- The weighted denominator: matched pairs count `1`, false positives `a`, false
negatives `b`. -/
noncomputable def wden (a b : ℝ) (n fp fn : ℕ) : ℝ := (n : ℝ) + a * fp + b * fn

/-- The weighted metric: the matched IoU sum over the weighted denominator. -/
noncomputable def wm (a b s : ℝ) (n fp fn : ℕ) : ℝ := s / wden a b n fp fn

/-- With weight `a = 0` on false positives, a false positive leaves the score
unchanged: the hypothesis `0 < a` above is exact. -/
axiom falsePositive_eq_of_zero_weight (b s : ℝ) (n fp fn : ℕ) :
    wm 0 b s n (fp + 1) fn = wm 0 b s n fp fn

end Lax303562.WeightedFamily
end
