-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.Normed.Module.FiniteDimension

-- Lax606786.FarUnitVectors
section
namespace Lax606786.FarUnitVectors

/-- A unit vector of `A` at distance at least `1 / (1 + dim W)` from `W`. -/
axiom exists_unit_far_of_finrank_lt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A W : Submodule ℝ X} [FiniteDimensional ℝ A] [FiniteDimensional ℝ W]
    (h : Module.finrank ℝ W < Module.finrank ℝ A) :
    ∃ u ∈ A, ‖u‖ = 1 ∧ (1 : ℝ) / (1 + Module.finrank ℝ W) ≤ Metric.infDist u (W : Set X)

end Lax606786.FarUnitVectors
end
