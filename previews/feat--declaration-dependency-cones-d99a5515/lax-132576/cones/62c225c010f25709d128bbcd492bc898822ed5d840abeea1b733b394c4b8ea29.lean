-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Finite.Basic

-- Lax132576.LabelledAutomata
section
namespace Lax132576.LabelledAutomata

/-- An automaton whose finitely many transitions are labelled by an input string and
a label from `L`, with distinguished sets of initial and final states. -/
structure LabAut (A L Q : Type) where
  /-- The set of initial states. -/
  init : Set Q
  /-- The set of final states. -/
  final : Set Q
  /-- The transition relation. -/
  δ : Set (Q × List A × L × Q)
  /-- There are only finitely many transitions. -/
  δ_finite : δ.Finite

namespace LabAut

variable {A L Q : Type}

/-- A path in the automaton, given as the list of the transitions it uses. -/
inductive Path (M : LabAut A L Q) : Q → List (Q × List A × L × Q) → Q → Prop
  | nil (q : Q) : Path M q [] q
  | cons {q : Q} {u : List A} {l : L} {q' : Q} {ts : List (Q × List A × L × Q)} {p : Q} :
      (q, u, l, q') ∈ M.δ → Path M q' ts p → Path M q ((q, u, l, q') :: ts) p

/-- The input string of a path: the concatenation of the input strings of its
transitions. -/
def inputOf (ts : List (Q × List A × L × Q)) : List A := (ts.map (fun t => t.2.1)).flatten

/-- The labels along a path, in the order of the transitions. -/
def labelsOf (ts : List (Q × List A × L × Q)) : List L := ts.map (fun t => t.2.2.1)

/-- A path is accepting if it starts in an initial state and ends in a final state.
-/
def Accepting (M : LabAut A L Q) (ts : List (Q × List A × L × Q)) : Prop :=
  ∃ q ∈ M.init, ∃ p ∈ M.final, M.Path q ts p

/-- The accepting paths with a given input string. -/
def acceptingOn (M : LabAut A L Q) (w : List A) : Set (List (Q × List A × L × Q)) :=
  {ts | M.Accepting ts ∧ inputOf ts = w}

end LabAut

end Lax132576.LabelledAutomata
end

-- Lax132576.RationalRelations
section
namespace Lax132576.RationalRelations

open Lax132576.LabelledAutomata

/-- A nondeterministic automaton with output: a labelled automaton whose labels
are output strings. -/
abbrev NFAO (A B Q : Type) := LabAut A (List B) Q

namespace NFAO

variable {A B Q : Type}

/-- The output string of a path: the concatenation of the outputs of its
transitions. -/
def outputOf (ts : List (Q × List A × List B × Q)) : List B := (LabAut.labelsOf ts).flatten

/-- The relation computed by an automaton with output: `w` is related to `v` if
some accepting run reads `w` and writes `v`. -/
def rel (M : NFAO A B Q) (w : List A) (v : List B) : Prop :=
  ∃ ts, M.Accepting ts ∧ LabAut.inputOf ts = w ∧ outputOf ts = v

end NFAO

/-- A relation is rational if it is computed by a nondeterministic automaton with
output with a finite state space. -/
def IsRationalRel {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q), ∀ w v, R w v ↔ M.rel w v

end Lax132576.RationalRelations
end

-- Lax132576.RationalFunctions
section
namespace Lax132576.RationalFunctions

open Lax132576.RationalRelations

/-- A string-to-string function is rational if its graph is a rational relation.
-/
def IsRationalFun {A B : Type} (f : List A → List B) : Prop :=
  IsRationalRel (fun w v => v = f w)

end Lax132576.RationalFunctions
end

-- Lax132576.WeightedAutomata
section
namespace Lax132576.WeightedAutomata

open Lax132576.LabelledAutomata

variable {A S Q : Type} [Semiring S]

/-- The weight of a path: the product of the weights of its transitions, in the
order in which they are taken. -/
def weightOf (ts : List (Q × List A × S × Q)) : S := (LabAut.labelsOf ts).prod

/-- The semantics of a weighted automaton: the sum of the weights of the accepting
runs over the input. -/
noncomputable def wEval (M : LabAut A S Q) (w : List A) : S :=
  ∑ᶠ ts ∈ M.acceptingOn w, weightOf ts

/-- The requirement of Definition B.3.2: every input string has only finitely
many accepting runs. -/
def FinitelyManyRuns (M : LabAut A S Q) : Prop := ∀ w : List A, (M.acceptingOn w).Finite

/-- A function `A* → S` computed by a weighted automaton over the semiring `S`
with a finite state space. -/
def IsWeighted {A S : Type} [Semiring S] (f : List A → S) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : LabAut A S Q), FinitelyManyRuns M ∧ wEval M = f

end Lax132576.WeightedAutomata
end

-- Lax132576.WeightedPrecomposition
section
namespace Lax132576.WeightedPrecomposition

open Lax132576.RationalFunctions Lax132576.WeightedAutomata

/-- Pre-composing a weighted function with a rational function gives a weighted
function. -/
axiom isWeighted_comp_of_isRationalFun {A B S : Type} [Finite A] [Finite B] [Semiring S]
    {f : List A → List B} {h : List B → S} (hf : IsRationalFun f) (hh : IsWeighted h) :
    IsWeighted (h ∘ f)

end Lax132576.WeightedPrecomposition
end
