-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finite.Defs

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

-- Lax916827.TwoWayCodes
section
namespace Lax916827.TwoWayCodes.twoWayCodeAut
end Lax916827.TwoWayCodes.twoWayCodeAut

namespace Lax916827.TwoWayCodes

open Lax916827.TwoWayTransducers

/-- A code of a two-way transducer over `ℕ`: a lookup table from triples (letter to
the left, state, letter to the right) to transitions. -/
abbrev TwoWayCode := List ((Option ℕ × ℕ × Option ℕ) × (List ℕ ⊕ (ℕ × List ℕ × Bool)))

end Lax916827.TwoWayCodes
end
