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

-- Lax303562.Candidate
section
namespace Lax303562.Candidate

open Lax303562.PanopticQuality

/-- The expected Panoptic Quality after including a candidate that matches with
probability `p` and, when it matches, with IoU `j`. -/
noncomputable def pqWithCandidate (s p j : ℝ) (n fp fn : ℕ) : ℝ :=
  (s + p * j) / (den n fp fn + 1 / 2)

/-- The rule solved for the match probability: for a positive IoU `j`, the
candidate raises the score if and only if `p > PQ / (2 j)`. -/
axiom equilibrium (s p j : ℝ) (n fp fn : ℕ) (hd : 0 < den n fp fn) (hj : 0 < j) :
    pq s n fp fn < pqWithCandidate s p j n fp fn ↔ pq s n fp fn / (2 * j) < p

end Lax303562.Candidate
end
