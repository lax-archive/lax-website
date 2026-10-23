-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs

-- Lax434175.Kernels
section
namespace Lax434175.Kernels

/-- A machine model: instances, schedules, and the accessors through which
constraints and objectives read a schedule. -/
structure Kernel where
  /-- The instances of the machine model. -/
  Inst : Type
  /-- The number of jobs of an instance. -/
  jobs : Inst → ℕ
  /-- The release date of a job. -/
  release : (x : Inst) → Fin (jobs x) → ℕ
  /-- The schedules of an instance. -/
  Sched : Inst → Type
  /-- The feasibility conditions of the machine model itself. -/
  feasible : (x : Inst) → Sched x → Prop
  /-- The time at which a job starts. -/
  start : (x : Inst) → Sched x → Fin (jobs x) → NNRat
  /-- The time at which a job completes. -/
  completion : (x : Inst) → Sched x → Fin (jobs x) → NNRat

end Lax434175.Kernels
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

-- Lax434175.ReleaseDates
section
namespace Lax434175.ReleaseDates.Value
end Lax434175.ReleaseDates.Value

namespace Lax434175.ReleaseDates.le
end Lax434175.ReleaseDates.le

namespace Lax434175.ReleaseDates.Value.holds
end Lax434175.ReleaseDates.Value.holds

namespace Lax434175.ReleaseDates.Value.none
end Lax434175.ReleaseDates.Value.none

namespace Lax434175.ReleaseDates.Value.online
end Lax434175.ReleaseDates.Value.online

namespace Lax434175.ReleaseDates.Value.releaseDates
end Lax434175.ReleaseDates.Value.releaseDates

namespace Lax434175.ReleaseDates

open Lax434175.Kernels Lax434175.Modules

/-- The number of distinct release dates. -/
def distinct (K : Kernel) : K.Inst → ℕ :=
  fun x => (Finset.univ.image (K.release x)).card

end Lax434175.ReleaseDates
end
