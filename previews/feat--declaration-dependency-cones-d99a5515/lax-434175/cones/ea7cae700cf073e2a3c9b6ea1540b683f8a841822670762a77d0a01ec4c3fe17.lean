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

-- Lax434175.Counts
section
namespace Lax434175.Counts.Bound.holds
end Lax434175.Counts.Bound.holds

namespace Lax434175.Counts.Bound.le
end Lax434175.Counts.Bound.le

namespace Lax434175.Counts

open Lax434175.Kernels Lax434175.Modules

inductive Bound
  | atMost (k : ℕ)
  | constant
  | unlimited
  | atMostJobsPlusOne
  | any

end Lax434175.Counts
end
