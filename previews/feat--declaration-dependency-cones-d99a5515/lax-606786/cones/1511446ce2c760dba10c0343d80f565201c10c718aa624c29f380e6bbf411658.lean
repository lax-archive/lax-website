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

end Lax606786.BackwardVitali
end
