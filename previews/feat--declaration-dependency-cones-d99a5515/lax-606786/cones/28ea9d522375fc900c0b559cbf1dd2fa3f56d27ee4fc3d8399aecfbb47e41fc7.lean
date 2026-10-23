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

/-- Inside a set of positive measure there is a set of positive measure whose first `N`
iterates are pairwise disjoint. -/
axiom exists_subset_disjoint_iterates {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω)
    (hσ : Ergodic (⇑σ) μ) (N : ℕ) {A : Set Ω} (hA : MeasurableSet A) (hApos : 0 < μ A) :
    ∃ A' ⊆ A, MeasurableSet A' ∧ 0 < μ A' ∧
      ∀ i < N, ∀ k < N, i ≠ k → Disjoint ((⇑σ)^[i] '' A') ((⇑σ)^[k] '' A')

end Lax606786.PeriodicPointsNull
end
