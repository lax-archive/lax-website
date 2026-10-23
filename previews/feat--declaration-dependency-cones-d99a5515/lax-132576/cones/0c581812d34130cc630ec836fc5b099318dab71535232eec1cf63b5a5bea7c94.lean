-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs

-- Lax132576.SequentialTransducers
section
namespace Lax132576.SequentialTransducers

/-- A sequential transducer: a Mealy machine whose transitions produce output
strings of variable length. -/
structure Sequential (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a target state and an output string. -/
  step : Q → A → Q × List B

namespace Sequential

variable {A B Q : Type}

/-- The output produced from a given state on an input string. -/
def run (T : Sequential A B Q) : Q → List A → List B
  | _, [] => []
  | q, a :: w => (T.step q a).2 ++ T.run (T.step q a).1 w

/-- The semantics of a sequential transducer. -/
def eval (T : Sequential A B Q) (w : List A) : List B := T.run T.init w

end Sequential

/-- A function computed by a sequential transducer with a finite state space. -/
def IsSequential {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (T : Sequential A B Q), T.eval = f

end Lax132576.SequentialTransducers
end
