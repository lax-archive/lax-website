-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic

-- Lax916827.TwoWayTransducers
section
namespace Lax916827
end Lax916827

namespace Lax916827.TwoWayTransducers
end Lax916827.TwoWayTransducers

namespace Lax916827.TwoWayTransducers.Cfg
end Lax916827.TwoWayTransducers.Cfg

namespace Lax916827.TwoWayTransducers.TwoWay
end Lax916827.TwoWayTransducers.TwoWay

namespace Lax916827.TwoWayTransducers.Cfg.conf
end Lax916827.TwoWayTransducers.Cfg.conf

namespace Lax916827.TwoWayTransducers.Cfg.halt
end Lax916827.TwoWayTransducers.Cfg.halt

namespace Lax916827.TwoWayTransducers.TwoWay.Reaches
end Lax916827.TwoWayTransducers.TwoWay.Reaches

namespace Lax916827.TwoWayTransducers.TwoWay.cfgAt
end Lax916827.TwoWayTransducers.TwoWay.cfgAt

namespace Lax916827.TwoWayTransducers.TwoWay.stepCfg
end Lax916827.TwoWayTransducers.TwoWay.stepCfg
end

-- Lax916827.ConfigurationGraphs
section
namespace Lax916827.ConfigurationGraphs.VOut
end Lax916827.ConfigurationGraphs.VOut

namespace Lax916827.ConfigurationGraphs.TwoWay.emptyOut
end Lax916827.ConfigurationGraphs.TwoWay.emptyOut

namespace Lax916827.ConfigurationGraphs.TwoWay.pathTrans
end Lax916827.ConfigurationGraphs.TwoWay.pathTrans

namespace Lax916827.ConfigurationGraphs.TwoWay.readL
end Lax916827.ConfigurationGraphs.TwoWay.readL

namespace Lax916827.ConfigurationGraphs.TwoWay.readR
end Lax916827.ConfigurationGraphs.TwoWay.readR

namespace Lax916827.ConfigurationGraphs.TwoWay.transOut
end Lax916827.ConfigurationGraphs.TwoWay.transOut

namespace Lax916827.ConfigurationGraphs.VOut.halt
end Lax916827.ConfigurationGraphs.VOut.halt

namespace Lax916827.ConfigurationGraphs.VOut.move
end Lax916827.ConfigurationGraphs.VOut.move

namespace Lax916827.ConfigurationGraphs.VOut.nil
end Lax916827.ConfigurationGraphs.VOut.nil

namespace Lax916827.ConfigurationGraphs

open Lax916827.TwoWayTransducers

namespace TwoWay

variable {A B Q : Type}

/-- The letter to the left of the gap `j` of `w`, if any. -/
def prevAt (w : List A) (j : ℕ) : Option A := if j = 0 then none else w[j - 1]?

variable {L : Type}

end TwoWay

end Lax916827.ConfigurationGraphs
end
