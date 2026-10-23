-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax296731.MoserTardosDefinitions
section
namespace Lax296731
end Lax296731

namespace Lax296731.MoserTardosDefinitions
end Lax296731.MoserTardosDefinitions

namespace Lax296731.MoserTardosDefinitions.ResamplingRule
end Lax296731.MoserTardosDefinitions.ResamplingRule
end

-- Lax296731.HaeuplerSahaSrinivasanDefinitions
section
set_option autoImplicit false

open scoped ENNReal

namespace Lax296731.HaeuplerSahaSrinivasanDefinitions

open Lax296731.MoserTardosDefinitions

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

end Lax296731.HaeuplerSahaSrinivasanDefinitions
end
