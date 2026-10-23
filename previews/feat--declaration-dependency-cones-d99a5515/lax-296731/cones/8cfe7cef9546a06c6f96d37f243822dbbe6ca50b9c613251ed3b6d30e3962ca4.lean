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

/-- A complete assignment to the finite family of independent variables. -/
abbrev Assignment := ∀ i, Value i

/-- Restriction of a complete assignment to an event's scope. -/
def restrictAssignment (variablesOf : Event → Finset Variable)
    (assignment : Assignment Value) (A : Event) :
    LocalAssignment Value (variablesOf A) :=
  fun i ↦ assignment i.1

/-- The bad event `A` is true under `assignment`. -/
def violates (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (assignment : Assignment Value) (A : Event) : Prop :=
  restrictAssignment Value variablesOf assignment A ∈ badEvent A

end Lax296731.MoserTardosDefinitions
end
