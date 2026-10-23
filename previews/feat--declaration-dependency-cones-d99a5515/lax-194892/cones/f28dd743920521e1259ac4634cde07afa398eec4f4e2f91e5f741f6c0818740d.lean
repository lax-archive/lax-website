-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic

-- Lax194892.PebbleTransducers
section
namespace Lax194892.PebbleTransducers.PebbleAction
end Lax194892.PebbleTransducers.PebbleAction

namespace Lax194892.PebbleTransducers.Pebble.Reaches
end Lax194892.PebbleTransducers.Pebble.Reaches

namespace Lax194892.PebbleTransducers.Pebble.stepCfg
end Lax194892.PebbleTransducers.Pebble.stepCfg

namespace Lax194892.PebbleTransducers.PebbleAction.move
end Lax194892.PebbleTransducers.PebbleAction.move

namespace Lax194892.PebbleTransducers.PebbleAction.out
end Lax194892.PebbleTransducers.PebbleAction.out

namespace Lax194892.PebbleTransducers.PebbleAction.pop
end Lax194892.PebbleTransducers.PebbleAction.pop

namespace Lax194892.PebbleTransducers.PebbleAction.push
end Lax194892.PebbleTransducers.PebbleAction.push

namespace Lax194892.PebbleTransducers.PebbleAction.terminate
end Lax194892.PebbleTransducers.PebbleAction.terminate

namespace Lax194892.PebbleTransducers

/-- A configuration: the state and the stack of gaps (from the bottom), or the
halting vertex. -/
inductive PebbleCfg (Q : Type) : Type
  | conf : Q → List ℕ → PebbleCfg Q
  | halt : PebbleCfg Q

namespace Pebble

variable {A B Q : Type} {k : ℕ}

end Pebble

end Lax194892.PebbleTransducers
end
