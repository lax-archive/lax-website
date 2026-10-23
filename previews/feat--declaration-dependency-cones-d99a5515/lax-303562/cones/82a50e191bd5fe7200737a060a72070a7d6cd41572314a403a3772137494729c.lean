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

end Lax303562.PanopticQuality
end

-- Lax303562.Removal
section
namespace Lax303562.Removal

open Lax303562.PanopticQuality

/-- The Panoptic Quality after removing a prediction that contributed `p · j` to
the numerator and `½` to the denominator. -/
noncomputable def pqWithoutPrediction (s p j : ℝ) (n fp fn : ℕ) : ℝ :=
  (s - p * j) / (den n fp fn - 1 / 2)

end Lax303562.Removal
end
