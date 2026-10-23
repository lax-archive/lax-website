-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

-- Lax606786.BackwardVitali
section
namespace Lax606786.BackwardVitali

open MeasureTheory Filter

/-- The orbit window `{σⁱ ω : -j ≤ i ≤ j}`. -/
def orbitWindow {Ω : Type*} [MeasurableSpace Ω] (σ : Ω ≃ᵐ Ω) (ω : Ω) (j : ℕ) : Set Ω :=
  {x | ∃ i ≤ j, x = σ^[i] ω ∨ x = (σ.symm : Ω → Ω)^[i] ω}

/-- Disjoint orbit windows, of admissible radii, covering all but `ε` of the space. -/
axiom backwardVitali {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic σ μ)
    (ε : ℝ) (hε : 0 < ε) (j : ℕ → Ω → ℕ) (hj : ∀ k, Measurable (j k))
    (hjtop : ∀ ω, Tendsto (fun k => j k ω) atTop atTop) :
    ∃ (A : Set Ω) (jω : Ω → ℕ), MeasurableSet A ∧ Measurable jω ∧
      (∀ ω ∈ A, ∃ k, jω ω = j k ω) ∧
      (A.PairwiseDisjoint fun ω => orbitWindow σ ω (jω ω)) ∧
      ENNReal.ofReal (1 - ε) < μ (⋃ ω ∈ A, orbitWindow σ ω (jω ω))

end Lax606786.BackwardVitali
end
