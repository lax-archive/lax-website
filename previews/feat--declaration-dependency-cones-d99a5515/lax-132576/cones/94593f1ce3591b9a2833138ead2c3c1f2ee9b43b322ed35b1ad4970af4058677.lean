-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Function.Defs

-- Lax132576.StringHomomorphisms
section
namespace Lax132576.StringHomomorphisms

/-- The string homomorphism that applies `φ` to every letter and concatenates the
results. -/
def homOf {A B : Type} (φ : A → List B) : List A → List B := fun w => (w.map φ).flatten

end Lax132576.StringHomomorphisms
end

-- Lax765601.CompositionClosure
section
namespace Lax765601.CompositionClosure

/-- A family of string-to-string functions, indexed by the input and the output
alphabet. -/
abbrev Family : Type 1 := ∀ (A B : Type), (List A → List B) → Prop

/-- The closure `P*` of a family `P` under composition: the identity functions, the
members of `P`, and the compositions `g ∘ f` of two members of the closure through
a finite intermediate alphabet. -/
inductive CompClosure (P : Family) : Family
  /-- A prime function belongs to the closure. -/
  | base {A B : Type} {f : List A → List B} : P A B f → CompClosure P A B f
  /-- The identity on every alphabet belongs to the closure. -/
  | protected id (A : Type) : CompClosure P A A _root_.id
  /-- The closure is closed under composition through a finite alphabet. -/
  | comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C} :
      CompClosure P A B f → CompClosure P B C g → CompClosure P A C (g ∘ f)

end Lax765601.CompositionClosure
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

/-- The state transformation of an input letter: how reading the letter updates
the state. -/
def letterTrans (M : Mealy A B Q) (a : A) : Q → Q := fun q => (M.step q a).1

end Mealy

end Lax765601.MealyMachine
end

-- Lax765601.PrimeMealyMachines
section
namespace Lax765601.PrimeMealyMachines

open Lax765601.MealyMachine Lax765601.CompositionClosure

/-- A Mealy machine is reversible if the state transformation of every letter is a
permutation of the state space. -/
def Reversible {A B Q : Type} (M : Mealy A B Q) : Prop :=
  ∀ a : A, Function.Bijective (M.letterTrans a)

/-- A Mealy machine is a flip-flop if the state transformation of every letter is
the identity or a constant. -/
def FlipFlop {A B Q : Type} (M : Mealy A B Q) : Prop :=
  ∀ a : A, M.letterTrans a = id ∨ ∃ q₀ : Q, ∀ q : Q, M.letterTrans a q = q₀

/-- A function is computed by a reversible Mealy machine with a finite state
space. -/
def IsReversibleMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ Reversible M

/-- A function is computed by a flip-flop Mealy machine with a finite state
space. -/
def IsFlipFlopMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ FlipFlop M

/-- The family of prime Mealy machines: the functions computed by a reversible or
by a flip-flop machine. -/
def PrimeMealyFam : Family := fun _ _ f => IsReversibleMealy f ∨ IsFlipFlopMealy f

end Lax765601.PrimeMealyMachines
end

-- Lax132576.PrimeRationalFunctions
section
namespace Lax132576.PrimeRationalFunctions

open Lax765601.CompositionClosure Lax765601.PrimeMealyMachines Lax132576.StringHomomorphisms

/-- The family of prime rational functions: prime Mealy machines, their
right-to-left variants, string homomorphisms, and the separator function
`w ↦ w #`. -/
def PrimeRationalFam : Family := fun A B f =>
  PrimeMealyFam A B f ∨
  PrimeMealyFam A B (fun w => (f w.reverse).reverse) ∨
  (∃ φ : A → List B, f = homOf φ) ∨
  (∃ e : Option A ≃ B, f = fun w => w.map (fun a => e (some a)) ++ [e none])

end Lax132576.PrimeRationalFunctions
end

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

-- Lax132576.RationalPrimes
section
namespace Lax132576.RationalPrimes

open Lax765601.CompositionClosure Lax132576.RationalFunctions Lax132576.PrimeRationalFunctions

/-- A function is rational if and only if it is a composition of prime rational
functions. -/
axiom isRationalFun_iff_compClosure_primeRational {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsRationalFun f ↔ CompClosure PrimeRationalFam A B f

end Lax132576.RationalPrimes
end
