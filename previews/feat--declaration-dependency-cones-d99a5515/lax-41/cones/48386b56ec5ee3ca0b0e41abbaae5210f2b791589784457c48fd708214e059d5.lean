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

end Lax41.MoserTardosDefinitions
end

-- Lax41.HaeuplerSahaSrinivasanDefinitions
section
set_option autoImplicit false

open scoped ENNReal

namespace Lax41.HaeuplerSahaSrinivasanDefinitions

open Lax41.MoserTardosDefinitions

variable {Event : Type} [Fintype Event] [DecidableEq Event]

variable {Variable : Type} [Fintype Variable] [DecidableEq Variable]

variable (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]

/-- An event belonging to the finite family on which the algorithm runs. -/
abbrev BadEventIndex (badEvents : Finset Event) := {A // A ∈ badEvents}

/-- The variables determining a bad event. -/
def badEventVariables (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable) :
    BadEventIndex badEvents → Finset Variable :=
  fun A ↦ variablesOf A.1

/-- The local set defining a bad event. -/
def badEventSet (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A))) :
    ∀ A, Set (LocalAssignment Value (badEventVariables badEvents variablesOf A)) :=
  fun A ↦ event A.1

end Lax41.HaeuplerSahaSrinivasanDefinitions
end
