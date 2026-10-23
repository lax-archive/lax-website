-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax965890.MoserTardosDefinitions
section
set_option autoImplicit false

open scoped ENNReal

namespace Lax965890.MoserTardosDefinitions

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

/-- The product law of an infinite resampling table. -/
noncomputable def tableMeasure
    (distribution : ∀ i, MeasureTheory.Measure (Value i)) :
    MeasureTheory.Measure (ResamplingTable Value) :=
  MeasureTheory.Measure.infinitePi
    fun j : TableIndex (Variable := Variable) ↦ distribution j.1

/-- The product law restricted to a finite collection of variables. -/
noncomputable def localMeasure
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    (indices : Finset Variable) :
    MeasureTheory.Measure (LocalAssignment Value indices) :=
  MeasureTheory.Measure.infinitePi fun i : indices ↦ distribution i.1

/-- The probability of a bad event under the original product distribution. -/
noncomputable def eventProbability
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (A : Event) : ℝ≥0∞ :=
  localMeasure Value distribution (variablesOf A) (badEvent A)

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

/-- The event resampled at time `n`, or `none` once no bad event remains. -/
def resamplingLog (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value variablesOf badEvent)
    (table : ResamplingTable Value) (n : Nat) : Option Event :=
  selectionRule.choose (currentAssignment Value table
    (runCounts Value variablesOf badEvent selectionRule table n))

end Lax965890.MoserTardosDefinitions
end

-- Lax965890.HaeuplerSahaSrinivasanDefinitions
section
set_option autoImplicit false

open scoped ENNReal

namespace Lax965890.HaeuplerSahaSrinivasanDefinitions

open scoped Classical

open Lax965890.MoserTardosDefinitions

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

/--
The bad events other than `B` that share at least one determining variable
with `B`.
-/
def dependencyNeighborhood (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable) (B : Event) :
    Finset (BadEventIndex badEvents) :=
  Finset.univ.filter fun A ↦
    A.1 ≠ B ∧ ¬Disjoint (variablesOf A.1) (variablesOf B)

/-- The observed event `B` is true in the assignment at stage `n`. -/
def eventOccursAt (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (table : ResamplingTable Value) (B : Event) (n : Nat) : Prop :=
  violates Value variablesOf event
    (currentAssignment Value table
      (runCounts Value (badEventVariables badEvents variablesOf)
        (badEventSet Value badEvents variablesOf event) selectionRule table n)) B

/-- The set of sample tables on which `B` is true at least once. -/
def eventEverOccurs (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (B : Event) : Set (ResamplingTable Value) :=
  {table | ∃ n, eventOccursAt Value badEvents variablesOf event selectionRule table B n}

/--
The first stage at which the algorithm has terminated.  On a nonterminating
table it is set to zero; under the local-lemma hypotheses that exceptional set
has probability zero.
-/
noncomputable def outputTime (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (table : ResamplingTable Value) : Nat :=
  if h : ∃ n, resamplingLog Value (badEventVariables badEvents variablesOf)
        (badEventSet Value badEvents variablesOf event) selectionRule table n = none
      then Nat.find h
      else 0

/-- The assignment returned when the resampling algorithm terminates. -/
noncomputable def outputAssignment (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (table : ResamplingTable Value) : Assignment Value :=
  currentAssignment Value table
    (runCounts Value (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event) selectionRule table
      (outputTime Value badEvents variablesOf event selectionRule table))

/-- The set of sample tables whose output assignment makes `B` true. -/
noncomputable def eventOccursInOutput (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (B : Event) : Set (ResamplingTable Value) :=
  {table | violates Value variablesOf event
    (outputAssignment Value badEvents variablesOf event selectionRule table) B}

/-- The probability that `B` is true at least once during the algorithm. -/
noncomputable def probabilityEventEverOccurs
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    (badEvents : Finset Event) (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (B : Event) : ℝ≥0∞ :=
  tableMeasure Value distribution
    (eventEverOccurs Value badEvents variablesOf event selectionRule B)

/-- The probability that `B` is true in the algorithm's output. -/
noncomputable def probabilityEventInOutput
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    (badEvents : Finset Event) (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (B : Event) : ℝ≥0∞ :=
  tableMeasure Value distribution
    (eventOccursInOutput Value badEvents variablesOf event selectionRule B)

end Lax965890.HaeuplerSahaSrinivasanDefinitions
end

-- Lax965890.HaeuplerSahaSrinivasanTheorem22
section
set_option autoImplicit false

open scoped ENNReal

namespace Lax965890.HaeuplerSahaSrinivasanTheorem22

open Lax965890.MoserTardosDefinitions

open Lax965890.HaeuplerSahaSrinivasanDefinitions

/-- The distributional local lemma of Haeupler, Saha, and Srinivasan, Theorem 2.2. -/
axiom theorem_2_2
    {Event : Type} [Fintype Event] [DecidableEq Event]
    {Variable : Type} [Fintype Variable] [DecidableEq Variable]
    (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (distribution i)]
    (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (event_measurable : ∀ A, MeasurableSet (event A))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (x : BadEventIndex badEvents → NNReal)
    (x_positive : ∀ A, 0 < x A)
    (x_less_than_one : ∀ A, x A < 1)
    (local_lemma_hypothesis : ∀ A,
      eventProbability Value distribution
          (badEventVariables badEvents variablesOf)
          (badEventSet Value badEvents variablesOf event) A ≤
        ((x A * ∏ C ∈ dependencyNeighborhood badEvents variablesOf A.1,
          (1 - x C) : NNReal) : ℝ≥0∞))
    (B : Event) :
    let upperBound :=
      eventProbability Value distribution variablesOf event B *
        ((∏ C ∈ dependencyNeighborhood badEvents variablesOf B,
          (1 - x C)⁻¹ : NNReal) : ℝ≥0∞)
    probabilityEventEverOccurs Value distribution badEvents variablesOf event
        selectionRule B ≤ upperBound ∧
      probabilityEventInOutput Value distribution badEvents variablesOf event
        selectionRule B ≤ upperBound

end Lax965890.HaeuplerSahaSrinivasanTheorem22
end
