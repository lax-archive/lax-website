-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Defs

-- Lax765601.Aperiodicity
section
namespace Lax765601.Aperiodicity

/-- The `n`-fold concatenation `vⁿ` of a string with itself. -/
def npow {A : Type} (v : List A) : ℕ → List A
  | 0 => []
  | n + 1 => v ++ npow v n

/-- A string-to-string function is aperiodic if for all input strings `u, v, w` the
last letter of `f (u vⁿ w)` — as an element of `Option B`, so that "no letter" is
an admissible value — is the same for all sufficiently large `n`. -/
def Aperiodic {A B : Type} (f : List A → List B) : Prop :=
  ∀ u v w : List A, ∃ o : Option B, ∃ N : ℕ, ∀ n ≥ N, (f (u ++ npow v n ++ w)).getLast? = o

end Lax765601.Aperiodicity
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

/-- A string-to-string function is computed by a Mealy machine if it is the
semantics of a Mealy machine with a finite state space. -/
def IsMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f

end Lax765601.MealyMachine
end

-- Lax765601.PrimeMealyMachines
section
namespace Lax765601.PrimeMealyMachines

open Lax765601.MealyMachine Lax765601.CompositionClosure

/-- A Mealy machine is a flip-flop if the state transformation of every letter is
the identity or a constant. -/
def FlipFlop {A B Q : Type} (M : Mealy A B Q) : Prop :=
  ∀ a : A, M.letterTrans a = id ∨ ∃ q₀ : Q, ∀ q : Q, M.letterTrans a q = q₀

/-- A function is computed by a flip-flop Mealy machine with a finite state
space. -/
def IsFlipFlopMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ FlipFlop M

/-- The family of flip-flop Mealy machines. -/
def FlipFlopFam : Family := fun _ _ f => IsFlipFlopMealy f

end Lax765601.PrimeMealyMachines
end

-- Lax765601.AperiodicMealy
section
namespace Lax765601.AperiodicMealy

open Lax765601.MealyMachine Lax765601.CompositionClosure Lax765601.PrimeMealyMachines Lax765601.Aperiodicity

/-- A function computed by a Mealy machine is aperiodic if and only if it is a
composition of flip-flop Mealy machines. -/
axiom aperiodic_iff_compClosure_flipFlop {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMealy f) :
    Aperiodic f ↔ CompClosure FlipFlopFam A B f

end Lax765601.AperiodicMealy
end
