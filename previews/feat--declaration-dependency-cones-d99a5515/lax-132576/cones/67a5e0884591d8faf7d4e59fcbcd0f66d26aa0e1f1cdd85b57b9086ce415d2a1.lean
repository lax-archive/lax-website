-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Logic.Function.Iterate

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

end Sequential

end Lax132576.SequentialTransducers
end

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

-- Lax132576.SubsequentialTransducers
section
namespace Lax132576.SubsequentialTransducers

open Lax765601.StateTransformations Lax132576.SequentialTransducers

/-- A subsequential transducer: a sequential transducer with a partial end-of-input
function applied to the last state of the run. -/
structure Subsequential (A B Q : Type) extends Sequential A B Q where
  /-- The partial end-of-input function. -/
  endOfInput : Q → Option (List B)

namespace Subsequential

variable {A B Q : Type}

end Subsequential

end Lax132576.SubsequentialTransducers
end
