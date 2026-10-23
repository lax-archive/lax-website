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

-- Lax303562.Removal
section
namespace Lax303562.Removal

open Lax303562.PanopticQuality

/-- The Panoptic Quality after removing a prediction that contributed `p · j` to
the numerator and `½` to the denominator. -/
noncomputable def pqWithoutPrediction (s p j : ℝ) (n fp fn : ℕ) : ℝ :=
  (s - p * j) / (den n fp fn - 1 / 2)

/-- Below the threshold, removal raises the score. -/
axiom lt_of_below (s p j : ℝ) (n fp fn : ℕ) (hd : 1 / 2 < den n fp fn)
    (h : p * j < pq s n fp fn / 2) : pq s n fp fn < pqWithoutPrediction s p j n fp fn

end Lax303562.Removal
end
