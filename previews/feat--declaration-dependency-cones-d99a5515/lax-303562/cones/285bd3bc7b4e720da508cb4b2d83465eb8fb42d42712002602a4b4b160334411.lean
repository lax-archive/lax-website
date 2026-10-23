-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

-- Lax303562.Matching
section
namespace Lax303562.Matching

/-- Intersection over union of two finite sets; `0` when both are empty. -/
noncomputable def iou {α : Type*} [DecidableEq α] (X Y : Finset α) : ℝ :=
  ((X ∩ Y).card : ℝ) / ((X ∪ Y).card : ℝ)

/-- With the non-strict threshold `≥ ½` a prediction can tie with two disjoint
annotations. -/
axiom ties_at_half :
    ∃ (P A B : Finset ℕ), Disjoint A B ∧ (1 : ℝ) / 2 ≤ iou P A ∧ (1 : ℝ) / 2 ≤ iou P B

end Lax303562.Matching
end
