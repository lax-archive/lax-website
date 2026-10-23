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

/-- Integrals are invariant under iterates of a measure-preserving map. -/
axiom integral_comp_iterate {μ : Measure Ω} {σ : Ω → Ω} (hmp : MeasurePreserving σ μ μ)
    {g : Ω → ℝ} (hg : Integrable g μ) (k : ℕ) :
    ∫ ω, g (σ^[k] ω) ∂μ = ∫ ω, g ω ∂μ

end Lax606786.RecurrenceAndInvariance
end
