-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

-- Lax606786.RokhlinLemma
section
namespace Lax606786.RokhlinLemma

open MeasureTheory

/-- A Rokhlin tower of height `n` covering all but `ε` of the space. -/
axiom rokhlin_lemma {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (σ : Ω ≃ᵐ Ω) (hσ : Ergodic σ μ) (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : Set Ω, MeasurableSet B ∧
      (∀ i < n, ∀ j < n, i ≠ j → Disjoint (σ^[i] '' B) (σ^[j] '' B)) ∧
      ENNReal.ofReal (1 - ε) < μ (⋃ i ∈ Finset.range n, σ^[i] '' B)

end Lax606786.RokhlinLemma
end
