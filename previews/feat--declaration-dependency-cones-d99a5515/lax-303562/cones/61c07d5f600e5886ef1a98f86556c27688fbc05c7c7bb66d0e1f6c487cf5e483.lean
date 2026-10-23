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

/-- The combined Panoptic Quality against two disagreeing annotators is strictly
below `1`, whatever the prediction. -/
axiom pq_lt_one_of_disagreement (sA sB : ℝ) (m a b tpA tpB : ℕ)
    (hab : a < b) (hA : tpA ≤ a) (hB : tpB ≤ m)
    (hsA : sA ≤ tpA) (hsB : sB ≤ tpB) (hm : 0 < m) :
    (sA + sB) / ((m : ℝ) + ((a : ℝ) + b) / 2) < 1

end Lax303562.AnnotatorCeiling
end
