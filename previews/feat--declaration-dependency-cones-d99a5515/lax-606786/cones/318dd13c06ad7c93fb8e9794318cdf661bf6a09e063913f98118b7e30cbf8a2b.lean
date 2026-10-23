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

/-- Almost every orbit visits `G` in every window `[n, (1 + η) n]` with `n` large. -/
axiom ae_eventually_exists_mem_window [IsProbabilityMeasure μ] {τ : Ω → Ω} (hτ : Ergodic τ μ) {G : Set Ω}
    (hG : MeasurableSet G) (hGpos : μ G ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, n ≤ k ∧ (k : ℝ) ≤ (1 + η) * n ∧ τ^[k] ω ∈ G

end Lax606786.BackwardGrowthFromForward
end
