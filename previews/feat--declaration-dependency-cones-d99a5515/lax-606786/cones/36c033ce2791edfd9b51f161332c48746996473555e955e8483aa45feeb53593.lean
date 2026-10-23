-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

-- Lax606786.BackwardGrowthFromForward
section
namespace Lax606786.BackwardGrowthFromForward

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Forward exponential lower bounds transfer along the orbit. -/
axiom ae_eventually_exp_le_backward [IsProbabilityMeasure μ] {τ : Ω → Ω} (hτ : Ergodic τ μ) (a : ℕ → Ω → ℝ)
    (ha : ∀ n, Measurable (a n)) {φ : Ω → ℝ} (hφm : Measurable φ) (hφ : Integrable φ μ)
    (hφ0 : ∀ ω, 0 ≤ φ ω) {c : ℝ}
    (hwin : ∀ᵐ ω ∂μ, ∀ n k : ℕ, n ≤ k →
      a k (τ^[k] ω) ≤ a n (τ^[n] ω) * Real.exp (∑ t ∈ Finset.Ioc n k, φ (τ^[t] ω)))
    (hfwd : ∀ᵐ ζ ∂μ, ∀ b : ℝ, b < c → ∀ᶠ n : ℕ in atTop, Real.exp (b * n) ≤ a n ζ) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, b < c → ∀ᶠ n : ℕ in atTop, Real.exp (b * n) ≤ a n (τ^[n] ω)

end Lax606786.BackwardGrowthFromForward
end
