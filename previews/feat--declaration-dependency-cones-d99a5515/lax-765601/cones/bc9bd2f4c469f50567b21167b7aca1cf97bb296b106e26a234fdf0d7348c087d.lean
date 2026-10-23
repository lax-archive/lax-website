-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Logic.Function.Defs

-- Lax765601.CompositionClosure
section
namespace Lax765601
end Lax765601

namespace Lax765601.CompositionClosure
end Lax765601.CompositionClosure

namespace Lax765601.CompositionClosure.CompClosure
end Lax765601.CompositionClosure.CompClosure
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

/-- A Mealy machine is a flip-flop if the state transformation of every letter is
the identity or a constant. -/
def FlipFlop {A B Q : Type} (M : Mealy A B Q) : Prop :=
  ∀ a : A, M.letterTrans a = id ∨ ∃ q₀ : Q, ∀ q : Q, M.letterTrans a q = q₀

/-- A function is computed by a flip-flop Mealy machine with a finite state
space. -/
def IsFlipFlopMealy {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ FlipFlop M

end Lax765601.PrimeMealyMachines
end
