-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Normed.Module.FiniteDimension

-- Lax606786.AuerbachLemma
section
namespace Lax606786.AuerbachLemma

/-- An Auerbach basis: unit vectors whose coefficients are controlled by the norm of the sum
(`‖a‖` is the supremum norm on `Fin k → ℝ`). -/
axiom exists_auerbach_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {k : ℕ} (hk : Module.finrank ℝ E = k) :
    ∃ e : Fin k → E, (∀ i, ‖e i‖ = 1) ∧ ∀ a : Fin k → ℝ, ‖a‖ ≤ ‖∑ i, a i • e i‖

end Lax606786.AuerbachLemma
end
