-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

-- Lax606786.PeriodicPointsNull
section
namespace Lax606786.PeriodicPointsNull

open MeasureTheory

/-- The points of period `N` form a null set. -/
axiom measure_periodicPts_eq_zero {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω)
    (hσ : Ergodic σ μ) {N : ℕ} (hN : 1 ≤ N) :
    μ {x | σ^[N] x = x} = 0

end Lax606786.PeriodicPointsNull
end
