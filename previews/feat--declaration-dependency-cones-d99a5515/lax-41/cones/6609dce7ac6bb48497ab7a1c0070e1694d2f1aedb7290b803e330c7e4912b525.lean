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

/-- The other bad events that share at least one random variable with `A`. -/
def dependencyNeighborhood (variablesOf : Event → Finset Variable)
    (A : Event) : Finset Event :=
  Finset.univ.filter fun B ↦
    B ≠ A ∧ ¬Disjoint (variablesOf A) (variablesOf B)

end Lax41.MoserTardosDefinitions
end
