-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.EReal.Basic
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

-- Lax606786.SubinvariantFunctions
section
namespace Lax606786.SubinvariantFunctions

open MeasureTheory

/-- A measurable `h ≤ h ∘ σ` is a.e. constant. -/
axiom exists_ae_eq_const_of_le_comp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : Ω → Ω} (hσ : Ergodic σ μ) {h : Ω → EReal} (hm : Measurable h)
    (hle : ∀ ω, h ω ≤ h (σ ω)) :
    ∃ c : EReal, ∀ᵐ ω ∂μ, h ω = c

end Lax606786.SubinvariantFunctions
end
