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

end Lax765601.PrimeMealyMachines
end
