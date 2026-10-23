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

/-- Increment precisely the counters in the scope of the selected event. -/
def advanceCounts (variablesOf : Event → Finset Variable)
    (counts : Variable → Nat) (selected : Option Event) : Variable → Nat :=
  selected.elim counts fun A i ↦
    if i ∈ variablesOf A then counts i + 1 else counts i

end Lax41.MoserTardosDefinitions
end
