-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- Lax606786.RecurrenceAndInvariance
section
namespace Lax606786.RecurrenceAndInvariance

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Almost every orbit of an ergodic map visits a set of positive measure. -/
axiom ae_exists_mem_iterate {μ : Measure Ω} [IsProbabilityMeasure μ] {σ : Ω → Ω}
    (hσ : Ergodic σ μ) {Λ : Set Ω} (hΛm : MeasurableSet Λ) (hΛ : μ Λ ≠ 0) :
    ∀ᵐ ω ∂μ, ∃ n : ℕ, σ^[n] ω ∈ Λ

end Lax606786.RecurrenceAndInvariance
end
