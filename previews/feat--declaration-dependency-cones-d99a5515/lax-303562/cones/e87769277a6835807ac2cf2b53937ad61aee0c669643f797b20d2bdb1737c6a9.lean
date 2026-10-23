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

-- Lax303562.AnnotatorCeiling
section
namespace Lax303562.AnnotatorCeiling

/-- With `a < b` annotated instances and `m` predicted ones, the true positives
against both annotators are strictly fewer than the combined denominator. -/
axiom ceiling_two_annotators (m a b tpA tpB : ℕ)
    (hab : a < b) (hA : tpA ≤ a) (hB : tpB ≤ m) :
    ((tpA : ℝ) + tpB) < (m : ℝ) + ((a : ℝ) + b) / 2

end Lax303562.AnnotatorCeiling
end
