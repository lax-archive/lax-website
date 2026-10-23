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

/-- A coordinate of the infinite resampling table. -/
abbrev TableIndex := (i : Variable) × Nat

/-- An infinite table of fresh samples, one row for each independent variable. -/
abbrev ResamplingTable := (j : TableIndex (Variable := Variable)) → Value j.1

/-- The product law of an infinite resampling table. -/
noncomputable def tableMeasure
    (distribution : ∀ i, MeasureTheory.Measure (Value i)) :
    MeasureTheory.Measure (ResamplingTable Value) :=
  MeasureTheory.Measure.infinitePi
    fun j : TableIndex (Variable := Variable) ↦ distribution j.1

end Lax296731.MoserTardosDefinitions
end
