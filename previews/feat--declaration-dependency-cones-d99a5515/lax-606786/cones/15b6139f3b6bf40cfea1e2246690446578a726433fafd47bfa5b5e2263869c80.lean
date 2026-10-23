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

/-- An a.e. property holds a.e. along whole forward orbits. -/
axiom ae_forall_iterate {μ : Measure Ω} {σ : Ω → Ω} (hσ : MeasurePreserving σ μ μ)
    {p : Ω → Prop} (h : ∀ᵐ ω ∂μ, p ω) : ∀ᵐ ω ∂μ, ∀ i : ℕ, p (σ^[i] ω)

end Lax606786.RecurrenceAndInvariance
end
