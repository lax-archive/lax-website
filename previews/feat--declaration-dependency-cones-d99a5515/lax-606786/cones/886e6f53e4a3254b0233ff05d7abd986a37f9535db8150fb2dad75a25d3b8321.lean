-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Invariants

-- Lax606786.BirkhoffErgodicTheorem
section
namespace Lax606786.BirkhoffErgodicTheorem

open MeasureTheory Filter Topology

/-- For an ergodic transformation the Birkhoff averages of an integrable function converge almost
everywhere to its integral. -/
axiom birkhoff_of_ergodic {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : Ω → Ω) (hσ : Ergodic σ μ) (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ σ f n ω) atTop (𝓝 (∫ x, f x ∂μ))

end Lax606786.BirkhoffErgodicTheorem
end
