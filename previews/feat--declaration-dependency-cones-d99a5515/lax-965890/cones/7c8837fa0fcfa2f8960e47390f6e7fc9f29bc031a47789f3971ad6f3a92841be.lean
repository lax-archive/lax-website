-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax965890.MoserTardosDefinitions
section
namespace Lax965890.MoserTardosDefinitions.ResamplingRule
end Lax965890.MoserTardosDefinitions.ResamplingRule

set_option autoImplicit false

open scoped ENNReal

namespace Lax965890.MoserTardosDefinitions

variable {Event : Type} [Fintype Event] [DecidableEq Event]

variable {Variable : Type} [Fintype Variable] [DecidableEq Variable]

variable (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]

/-- The other bad events that share at least one random variable with `A`. -/
def dependencyNeighborhood (variablesOf : Event → Finset Variable)
    (A : Event) : Finset Event :=
  Finset.univ.filter fun B ↦
    B ≠ A ∧ ¬Disjoint (variablesOf A) (variablesOf B)

end Lax965890.MoserTardosDefinitions
end
