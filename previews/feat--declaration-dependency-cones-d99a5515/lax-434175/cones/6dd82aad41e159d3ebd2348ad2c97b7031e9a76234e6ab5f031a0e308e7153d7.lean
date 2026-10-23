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
namespace Lax434175.Batching.Mode
end Lax434175.Batching.Mode

namespace Lax434175.Batching.ProcessingTimes
end Lax434175.Batching.ProcessingTimes

namespace Lax434175.Batching.Sched
end Lax434175.Batching.Sched

namespace Lax434175.Batching.length
end Lax434175.Batching.length

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

inductive Capacity
  | unbounded
  | bounded
  | sizes

/-- The data of a capacity value. -/
def Capacity.Data : Capacity → Inst → Type
  | .unbounded, _ => Unit
  | .bounded, _ => ℕ
  | .sizes, x => ℕ × (Fin x.jobs → ℕ)

/-- The capacity of a batch; the number of jobs when unbounded. -/
def Capacity.bound {x : Inst} : (v : Capacity) → v.Data x → ℕ
  | .unbounded, _ => x.jobs
  | .bounded, b => b
  | .sizes, d => d.1

/-- The size of a job; `1` without sizes. -/
def Capacity.size {x : Inst} : (v : Capacity) → v.Data x → Fin x.jobs → ℕ
  | .unbounded, _ => fun _ => 1
  | .bounded, _ => fun _ => 1
  | .sizes, d => d.2

def Capacity.le : Capacity → Capacity → Bool
  | .unbounded, _ => true
  | .bounded, .unbounded => false
  | .bounded, _ => true
  | .sizes, .sizes => true
  | .sizes, _ => false

def Capacity.embed : {v w : Capacity} → Capacity.le v w = true → (x : Inst) →
    v.Data x → w.Data x
  | _, .unbounded, _, _, _ => ()
  | v, .bounded, _, _, d => v.bound d
  | v, .sizes, _, _, d => (v.bound d, v.size d)

end Lax434175.Batching
end
