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

/-- Increment precisely the counters in the scope of the selected event. -/
def advanceCounts (variablesOf : Event → Finset Variable)
    (counts : Variable → Nat) (selected : Option Event) : Variable → Nat :=
  selected.elim counts fun A i ↦
    if i ∈ variablesOf A then counts i + 1 else counts i

end Lax296731.MoserTardosDefinitions
end
