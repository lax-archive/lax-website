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

-- Lax303562.Duplication
section
namespace Lax303562.Duplication

open Lax303562.PanopticQuality

/-- A duplicate better than the current score raises the metric under all-pairs
accumulation and lowers it under one-to-one matching. -/
axiom opposite_directions (s v : ℝ) (n fp fn : ℕ) (hs : 0 < s) (hd : 0 < den n fp fn)
    (hv : pq s n fp fn < v) :
    pq s n fp fn < pq (s + v) (n + 1) fp fn ∧ pq s n (fp + 1) fn < pq s n fp fn

end Lax303562.Duplication
end
