-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Logic.Function.Iterate

-- Lax765601.MealyMachine
section
namespace Lax765601
end Lax765601

namespace Lax765601.MealyMachine
end Lax765601.MealyMachine

namespace Lax765601.MealyMachine.Mealy
end Lax765601.MealyMachine.Mealy

namespace Lax765601.MealyMachine.Mealy.run
end Lax765601.MealyMachine.Mealy.run
end

-- Lax765601.StateTransformations
section
namespace Lax765601.StateTransformations
end Lax765601.StateTransformations
end

-- Lax132576.Bimachines
section
namespace Lax132576.Bimachines

open Lax765601.StateTransformations

/-- A bimachine: a deterministic prefix automaton, a deterministic suffix automaton
(run on the reverse of the suffix) and an output function on pairs of states. -/
structure Bimachine (A B P S : Type) where
  /-- Initial state of the prefix automaton. -/
  prefixInit : P
  /-- Transition function of the prefix automaton. -/
  prefixStep : P → A → P
  /-- Initial state of the suffix automaton. -/
  suffixInit : S
  /-- Transition function of the suffix automaton. -/
  suffixStep : S → A → S
  /-- The output function. -/
  out : P → S → List B

namespace Bimachine

variable {A B P S : Type}

end Bimachine

end Lax132576.Bimachines
end
