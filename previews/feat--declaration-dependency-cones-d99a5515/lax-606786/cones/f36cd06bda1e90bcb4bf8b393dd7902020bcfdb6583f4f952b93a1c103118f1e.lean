-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

-- Lax606786.TemperedFunctionAlgebra
section
namespace Lax606786.TemperedFunctionAlgebra

open MeasureTheory Filter

open Lax606786.TemperedFunctions

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `0` is tempered. -/
axiom tempered_zero {σ : Ω → Ω} {μ : Measure Ω} : Tempered σ μ (fun _ => (0 : ℝ))

end Lax606786.TemperedFunctionAlgebra
end
