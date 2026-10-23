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

end Lax41.MoserTardosDefinitions
end
