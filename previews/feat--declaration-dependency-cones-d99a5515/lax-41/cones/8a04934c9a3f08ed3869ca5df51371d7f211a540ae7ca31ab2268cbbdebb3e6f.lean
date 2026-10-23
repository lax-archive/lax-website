-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib

-- Lax41.MoserTardosDefinitions
section
namespace Lax41.MoserTardosDefinitions.ResamplingRule
end Lax41.MoserTardosDefinitions.ResamplingRule

set_option autoImplicit false

open scoped ENNReal

namespace Lax41.MoserTardosDefinitions

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

end Lax41.MoserTardosDefinitions
end
