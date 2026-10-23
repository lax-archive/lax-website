-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Infix
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

-- Lax765601.ElementaryProperties
section
namespace Lax765601.ElementaryProperties

/-- `f` is length preserving, i.e. letter-to-letter: the output has the length of
the input. -/
def LengthPreserving {A B : Type} (f : List A → List B) : Prop :=
  ∀ w : List A, (f w).length = w.length

/-- `f` is prefix determined: the first `n` output letters depend only on the
first `n` input letters. -/
def PrefixDetermined {A B : Type} (f : List A → List B) : Prop :=
  ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n

end Lax765601.ElementaryProperties
end

-- Lax765601.MealyMachine
section
namespace Lax765601.MealyMachine

/-- A Mealy machine with input alphabet `A`, output alphabet `B` and state space
`Q`: an initial state and a transition function `Q × A → Q × B`. -/
structure Mealy (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a source state and an input letter determine a
  target state and an output letter. -/
  step : Q → A → Q × B

namespace Mealy

variable {A B Q : Type}

/-- The output produced by the machine on an input string, when started in a
given state. -/
def run (M : Mealy A B Q) : Q → List A → List B
  | _, [] => []
  | q, a :: w => (M.step q a).2 :: M.run (M.step q a).1 w

/-- The semantics of a Mealy machine: the output produced from the initial state.
-/
def eval (M : Mealy A B Q) (w : List A) : List B := M.run M.init w

end Mealy

/-- A string-to-string function is computed by a Mealy machine if it is the
semantics of a Mealy machine with a finite state space. -/
def IsMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f

end Lax765601.MealyMachine
end

-- Lax132576.RationalMealyCharacterisation
section
namespace Lax132576.RationalMealyCharacterisation

open Lax765601.MealyMachine Lax765601.ElementaryProperties Lax132576.RationalFunctions

/-- A rational function is computed by a Mealy machine if and only if it is
letter-to-letter and prefix determined. -/
axiom isMealy_iff_of_isRationalFun {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) : IsMealy f ↔ LengthPreserving f ∧ PrefixDetermined f

end Lax132576.RationalMealyCharacterisation
end
