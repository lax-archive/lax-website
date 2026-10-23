-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Normed.Module.FiniteDimension

-- Lax606786.AuerbachLemma
section
namespace Lax606786.AuerbachLemma

/-- A projection of norm at most `m` onto an `m`-dimensional subspace. -/
axiom exists_proj_norm_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (W : Submodule ℝ X) [FiniteDimensional ℝ W] {m : ℕ} (hm : Module.finrank ℝ W = m) :
    ∃ P : X →L[ℝ] X, (∀ x, P x ∈ W) ∧ (∀ w ∈ W, P w = w) ∧ ‖P‖ ≤ m

end Lax606786.AuerbachLemma
end
