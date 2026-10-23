-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
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

-- Lax434175.Batching
section
namespace Lax434175.Batching.Capacity
end Lax434175.Batching.Capacity

namespace Lax434175.Batching.Mode
end Lax434175.Batching.Mode

namespace Lax434175.Batching.ProcessingTimes
end Lax434175.Batching.ProcessingTimes

namespace Lax434175.Batching.length
end Lax434175.Batching.length

namespace Lax434175.Batching.Capacity.Data
end Lax434175.Batching.Capacity.Data

namespace Lax434175.Batching.Capacity.bound
end Lax434175.Batching.Capacity.bound

namespace Lax434175.Batching.Capacity.bounded
end Lax434175.Batching.Capacity.bounded

namespace Lax434175.Batching.Capacity.embed
end Lax434175.Batching.Capacity.embed

namespace Lax434175.Batching.Capacity.le
end Lax434175.Batching.Capacity.le

namespace Lax434175.Batching.Capacity.sizes
end Lax434175.Batching.Capacity.sizes

namespace Lax434175.Batching.Capacity.unbounded
end Lax434175.Batching.Capacity.unbounded

namespace Lax434175.Batching.Mode.parallel
end Lax434175.Batching.Mode.parallel

namespace Lax434175.Batching.Mode.serial
end Lax434175.Batching.Mode.serial

namespace Lax434175.Batching.ProcessingTimes.arbitrary
end Lax434175.Batching.ProcessingTimes.arbitrary

namespace Lax434175.Batching.ProcessingTimes.equal
end Lax434175.Batching.ProcessingTimes.equal

namespace Lax434175.Batching.ProcessingTimes.holds
end Lax434175.Batching.ProcessingTimes.holds

namespace Lax434175.Batching.ProcessingTimes.rank
end Lax434175.Batching.ProcessingTimes.rank

namespace Lax434175.Batching.ProcessingTimes.unit
end Lax434175.Batching.ProcessingTimes.unit

namespace Lax434175.Batching

open Lax434175.Kernels Lax434175.Modules

structure Inst where
  jobs : ℕ
  p : Fin jobs → ℕ
  /-- The release date of a job. -/
  r : Fin jobs → ℕ
  /-- The setup time before every batch. -/
  setup : ℕ

structure Sched (x : Inst) where
  /-- The number of the batch of a job. -/
  batch : Fin x.jobs → ℕ
  /-- The start time of a batch. -/
  start : ℕ → ℕ

end Lax434175.Batching
end
