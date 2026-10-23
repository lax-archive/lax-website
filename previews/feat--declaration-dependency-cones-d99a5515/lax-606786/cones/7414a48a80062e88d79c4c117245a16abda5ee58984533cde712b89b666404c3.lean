-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- Lax606786.LowerIntegrals
section
namespace Lax606786.LowerIntegrals

open MeasureTheory

/-- `L_μ(g) = inf_M ∫ max(g, -M) dμ`. -/
noncomputable def lowerIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ) :
    EReal :=
  ⨅ M : ℕ, ((∫ ω, max (g ω) (-(M : ℝ)) ∂μ : ℝ) : EReal)

end Lax606786.LowerIntegrals
end

-- Lax606786.LowerIntegralProperties
section
namespace Lax606786.LowerIntegralProperties

open MeasureTheory

open Lax606786.LowerIntegrals

variable {Ω : Type*} [MeasurableSpace Ω]

/-- On integrable functions the lower integral is the integral. -/
axiom lowerIntegral_eq_integral {μ : Measure Ω} [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : Integrable g μ) : lowerIntegral μ g = ((∫ ω, g ω ∂μ : ℝ) : EReal)

end Lax606786.LowerIntegralProperties
end
