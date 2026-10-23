-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic

-- Lax323828.SmallSupport
section
namespace Lax323828.SmallSupport

open scoped Classical

/-- The coordinate sets of size at most `l` whose squared coefficient is at least `l * δ`. -/
noncomputable def largeSets {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset (Finset ι) :=
  Finset.univ.filter fun a ↦ a.card ≤ l ∧ (l : ℝ) * δ ≤ c a ^ 2

/-- The union of the coordinate sets selected by `largeSets`. -/
noncomputable def decodingSet {ι : Type} [Fintype ι] [DecidableEq ι] (c : Finset ι → ℝ) (l : ℕ)
    (δ : ℝ) : Finset ι :=
  (largeSets c l δ).biUnion id

end Lax323828.SmallSupport
end
