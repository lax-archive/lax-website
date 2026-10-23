-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs

-- Lax765601.MealyMachine
section
namespace Lax765601.MealyMachine.Mealy.run
end Lax765601.MealyMachine.Mealy.run

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

/-- The underlying pre-automaton: the transition function with the output letters
forgotten. -/
def transFun (M : Mealy A B Q) : Q → A → Q := fun q a => (M.step q a).1

end Mealy

end Lax765601.MealyMachine
end
