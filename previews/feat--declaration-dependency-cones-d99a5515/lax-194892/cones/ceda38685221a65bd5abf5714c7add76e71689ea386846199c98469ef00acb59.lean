-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find

-- Lax194892.PebbleTransducers
section
namespace Lax194892
end Lax194892

namespace Lax194892.PebbleTransducers
end Lax194892.PebbleTransducers

namespace Lax194892.PebbleTransducers.Pebble
end Lax194892.PebbleTransducers.Pebble

namespace Lax194892.PebbleTransducers.PebbleAction
end Lax194892.PebbleTransducers.PebbleAction

namespace Lax194892.PebbleTransducers.PebbleCfg
end Lax194892.PebbleTransducers.PebbleCfg

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

namespace Lax194892.PebbleTransducers.PebbleCfg.conf
end Lax194892.PebbleTransducers.PebbleCfg.conf

namespace Lax194892.PebbleTransducers.PebbleCfg.halt
end Lax194892.PebbleTransducers.PebbleCfg.halt
end

-- Lax194892.PebbleConfigurationEncoding
section
namespace Lax194892.PebbleConfigurationEncoding
end Lax194892.PebbleConfigurationEncoding

namespace Lax194892.PebbleConfigurationEncoding.RestrReaches
end Lax194892.PebbleConfigurationEncoding.RestrReaches
end

-- Lax194892.ChildConfigurationGraphs
section
namespace Lax194892.ChildConfigurationGraphs.CGLetter
end Lax194892.ChildConfigurationGraphs.CGLetter

namespace Lax194892.ChildConfigurationGraphs.CGPath
end Lax194892.ChildConfigurationGraphs.CGPath

namespace Lax194892.ChildConfigurationGraphs.HeightGe
end Lax194892.ChildConfigurationGraphs.HeightGe

namespace Lax194892.ChildConfigurationGraphs.IsChildSeq
end Lax194892.ChildConfigurationGraphs.IsChildSeq

namespace Lax194892.ChildConfigurationGraphs.StrictAbove
end Lax194892.ChildConfigurationGraphs.StrictAbove

namespace Lax194892.ChildConfigurationGraphs

open Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding

/-- The direction of an edge: inside the column, one column right, one column left. -/
abbrev Dir := Option Bool

/-- The column that the direction `d` leads to from the column `p`. -/
def dest (p : ℕ) : Dir → Option ℕ
  | none => some p
  | some true => some (p + 1)
  | some false => if p = 0 then none else some (p - 1)

end Lax194892.ChildConfigurationGraphs
end
