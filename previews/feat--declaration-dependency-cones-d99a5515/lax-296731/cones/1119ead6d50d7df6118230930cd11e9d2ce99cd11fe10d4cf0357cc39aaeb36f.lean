-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax296731.MoserTardosDefinitions
section
namespace Lax296731.MoserTardosDefinitions.ResamplingRule
end Lax296731.MoserTardosDefinitions.ResamplingRule

set_option autoImplicit false

open scoped ENNReal

namespace Lax296731.MoserTardosDefinitions

variable {Event : Type} [Fintype Event] [DecidableEq Event]

variable {Variable : Type} [Fintype Variable] [DecidableEq Variable]

variable (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]

/-- An assignment to the variables in a finite scope. -/
abbrev LocalAssignment (indices : Finset Variable) :=
  (i : indices) → Value i.1

/-- The product law restricted to a finite collection of variables. -/
noncomputable def localMeasure
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    (indices : Finset Variable) :
    MeasureTheory.Measure (LocalAssignment Value indices) :=
  MeasureTheory.Measure.infinitePi fun i : indices ↦ distribution i.1

/-- The probability of a bad event under the original product distribution. -/
noncomputable def eventProbability
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (A : Event) : ℝ≥0∞ :=
  localMeasure Value distribution (variablesOf A) (badEvent A)

end Lax296731.MoserTardosDefinitions
end
