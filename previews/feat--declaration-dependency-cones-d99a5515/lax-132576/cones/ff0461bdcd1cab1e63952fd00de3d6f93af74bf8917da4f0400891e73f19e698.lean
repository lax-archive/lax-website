-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs

-- Lax132576.SequentialTransducers
section
namespace Lax132576.SequentialTransducers.Sequential.run
end Lax132576.SequentialTransducers.Sequential.run

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

/-- The transition function of the underlying automaton. -/
def transFun (T : Sequential A B Q) : Q → A → Q := fun q a => (T.step q a).1

end Sequential

end Lax132576.SequentialTransducers
end
