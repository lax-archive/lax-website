-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Real.Basic

-- Lax303562.PanopticQuality
section
namespace Lax303562.PanopticQuality

/-- The denominator of Panoptic Quality: matched pairs count `1`, unmatched
predictions and unmatched annotations count `½` each. -/
noncomputable def den (n fp fn : ℕ) : ℝ := (n : ℝ) + (fp + fn) / 2

/-- Panoptic Quality: the sum `s` of the matched IoUs over the denominator. -/
noncomputable def pq (s : ℝ) (n fp fn : ℕ) : ℝ := s / den n fp fn

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

/-- Panoptic Quality is the member `a = b = ½` of the family. -/
axiom pq_eq_wm_half (s : ℝ) (n fp fn : ℕ) :
    pq s n fp fn = wm (1 / 2) (1 / 2) s n fp fn

end Lax303562.WeightedFamily
end
