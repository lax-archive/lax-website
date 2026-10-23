-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- Lax606786.MaximalErgodicTheorem
section
namespace Lax606786.MaximalErgodicTheorem

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {σ : Ω → Ω} {f : Ω → ℝ}

/-- Garsia's maximal ergodic theorem. -/
axiom maximal_ergodic (hmp : MeasurePreserving σ μ μ) (hf : Integrable f μ)
    (hfm : Measurable f) (n : ℕ) :
    0 ≤ ∫ x in {x | ∃ j, 1 ≤ j ∧ j ≤ n ∧ 0 < birkhoffSum σ f j x}, f x ∂μ

end Lax606786.MaximalErgodicTheorem
end
