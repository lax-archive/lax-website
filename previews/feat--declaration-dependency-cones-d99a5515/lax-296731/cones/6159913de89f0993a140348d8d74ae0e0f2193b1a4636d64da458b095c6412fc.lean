-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax296731.MoserTardosDefinitions
section
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

/--
A measurable deterministic implementation of "choose any currently true bad
event".  It returns `none` exactly when no bad event is true.
-/
structure ResamplingRule (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A))) where
  choose : Assignment Value → Option Event
  measurable_fiber : ∀ result, MeasurableSet {assignment | choose assignment = result}
  sound : ∀ ⦃assignment : Assignment Value⦄ ⦃A : Event⦄,
    choose assignment = some A →
      violates Value variablesOf badEvent assignment A
  complete : ∀ ⦃assignment : Assignment Value⦄,
    choose assignment = none →
      ∀ A, ¬violates Value variablesOf badEvent assignment A

/-- The assignment exposed by a resampling table at the given row counters. -/
def currentAssignment (table : ResamplingTable Value) (counts : Variable → Nat) :
    Assignment Value :=
  fun i ↦ table ⟨i, counts i⟩

/-- Increment precisely the counters in the scope of the selected event. -/
def advanceCounts (variablesOf : Event → Finset Variable)
    (counts : Variable → Nat) (selected : Option Event) : Variable → Nat :=
  selected.elim counts fun A i ↦
    if i ∈ variablesOf A then counts i + 1 else counts i

/-- The row counters after the first `n` iterations of the resampling algorithm. -/
def runCounts (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value variablesOf badEvent)
    (table : ResamplingTable Value) : Nat → Variable → Nat :=
  Nat.rec (fun _ ↦ 0) fun _ counts ↦
    advanceCounts variablesOf counts
      (selectionRule.choose (currentAssignment Value table counts))

end Lax296731.MoserTardosDefinitions
end
