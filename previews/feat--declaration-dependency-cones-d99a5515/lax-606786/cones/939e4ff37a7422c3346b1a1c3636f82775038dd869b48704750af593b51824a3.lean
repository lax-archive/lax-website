-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

-- Lax606786.TemperedFunctions
section
namespace Lax606786.TemperedFunctions

open MeasureTheory Filter Topology

/-- `f(σⁿω)/n → 0` for `μ`-a.e. `ω`. -/
def Tempered {Ω : Type*} [MeasurableSpace Ω] (σ : Ω → Ω) (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => f (σ^[n] ω) / n) atTop (𝓝 0)

end Lax606786.TemperedFunctions
end

-- Lax606786.TemperedCriteria
section
namespace Lax606786.TemperedCriteria

open MeasureTheory

open Lax606786.TemperedFunctions

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Mañé's lemma: a nonnegative function that can drop by at most an integrable amount along
each step of the orbit is tempered. -/
axiom tempered_of_le_add_comp (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → Ω)
    (hσ : Ergodic σ μ) (g h : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω)
    (hh : Measurable h) (hint : Integrable h μ) (hle : ∀ᵐ ω ∂μ, g ω ≤ h ω + g (σ ω)) :
    Tempered σ μ g

end Lax606786.TemperedCriteria
end
