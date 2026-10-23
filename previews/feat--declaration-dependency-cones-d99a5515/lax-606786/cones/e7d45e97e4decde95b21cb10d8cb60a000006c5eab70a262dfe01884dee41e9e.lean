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

/-- The Birkhoff averages converge a.e. and in `L¹` to the conditional expectation of `f` given
the `σ`-algebra of `σ`-invariant sets. -/
axiom birkhoff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Ω → Ω) (hσ : MeasurePreserving σ μ μ) (f : Ω → ℝ) (hf : Integrable f μ) :
    (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ σ f n ω) atTop
      (𝓝 ((μ[f | MeasurableSpace.invariants σ]) ω))) ∧
    Tendsto (fun n : ℕ =>
      ∫ ω, |birkhoffAverage ℝ σ f n ω - (μ[f | MeasurableSpace.invariants σ]) ω| ∂μ)
      atTop (𝓝 0)

end Lax606786.BirkhoffErgodicTheorem
end
