-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.NNRat.Defs

-- Lax434175.Kernels
section
namespace Lax434175
end Lax434175

namespace Lax434175.Kernels
end Lax434175.Kernels

namespace Lax434175.Kernels.Kernel
end Lax434175.Kernels.Kernel
end

-- Lax434175.Modules
section
namespace Lax434175.Modules
end Lax434175.Modules

namespace Lax434175.Modules.Module
end Lax434175.Modules.Module

namespace Lax434175.Modules.Objective
end Lax434175.Modules.Objective

namespace Lax434175.Modules.Module.Sound
end Lax434175.Modules.Module.Sound

namespace Lax434175.Modules.Objective.Sound
end Lax434175.Modules.Objective.Sound
end

-- Lax434175.ForbiddenTimes
section
namespace Lax434175.ForbiddenTimes.Data
end Lax434175.ForbiddenTimes.Data

namespace Lax434175.ForbiddenTimes.Value
end Lax434175.ForbiddenTimes.Value

namespace Lax434175.ForbiddenTimes.embed
end Lax434175.ForbiddenTimes.embed

namespace Lax434175.ForbiddenTimes.le
end Lax434175.ForbiddenTimes.le

namespace Lax434175.ForbiddenTimes.view
end Lax434175.ForbiddenTimes.view

namespace Lax434175.ForbiddenTimes.Value.forbidden
end Lax434175.ForbiddenTimes.Value.forbidden

namespace Lax434175.ForbiddenTimes.Value.none
end Lax434175.ForbiddenTimes.Value.none

namespace Lax434175.ForbiddenTimes

open Lax434175.Kernels Lax434175.Modules

inductive Encoding
  | standard
  | highMultiplicity
  deriving DecidableEq

end Lax434175.ForbiddenTimes
end
