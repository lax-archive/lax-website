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

/-- A coordinate of the infinite resampling table. -/
abbrev TableIndex := (i : Variable) × Nat

/-- An infinite table of fresh samples, one row for each independent variable. -/
abbrev ResamplingTable := (j : TableIndex (Variable := Variable)) → Value j.1

/-- A complete assignment to the finite family of independent variables. -/
abbrev Assignment := ∀ i, Value i

/-- The assignment exposed by a resampling table at the given row counters. -/
def currentAssignment (table : ResamplingTable Value) (counts : Variable → Nat) :
    Assignment Value :=
  fun i ↦ table ⟨i, counts i⟩

end Lax41.MoserTardosDefinitions
end
