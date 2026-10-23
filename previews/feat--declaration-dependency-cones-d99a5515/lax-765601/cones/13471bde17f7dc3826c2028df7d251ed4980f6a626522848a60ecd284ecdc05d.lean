-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Logic.Function.Iterate

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

end Mealy

end Lax765601.MealyMachine
end

-- Lax765601.StateTransformations
section
namespace Lax765601.StateTransformations

open Lax765601.MealyMachine

/-- The state transformation transducer of a pre-automaton: the Mealy machine
whose `n`-th output letter is the state transformation of the first `n` input
letters. -/
def stateTransTransducer {A Q : Type} (δ : Q → A → Q) : Mealy A (Q → Q) (Q → Q) where
  init := id
  step := fun t a => (fun q => δ (t q) a, fun q => δ (t q) a)

end Lax765601.StateTransformations
end
