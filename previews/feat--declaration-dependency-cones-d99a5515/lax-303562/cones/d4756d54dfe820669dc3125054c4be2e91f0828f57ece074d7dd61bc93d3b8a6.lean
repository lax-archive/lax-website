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

end Lax303562.WeightedFamily
end
