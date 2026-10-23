-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
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

-- Lax434175.ParallelMachines
section
namespace Lax434175.ParallelMachines.Environment
end Lax434175.ParallelMachines.Environment

namespace Lax434175.ParallelMachines.Model
end Lax434175.ParallelMachines.Model

namespace Lax434175.ParallelMachines.ProcessingTimes
end Lax434175.ParallelMachines.ProcessingTimes

namespace Lax434175.ParallelMachines.Environment.holds
end Lax434175.ParallelMachines.Environment.holds

namespace Lax434175.ParallelMachines.Environment.identical
end Lax434175.ParallelMachines.Environment.identical

namespace Lax434175.ParallelMachines.Environment.rank
end Lax434175.ParallelMachines.Environment.rank

namespace Lax434175.ParallelMachines.Environment.uniform
end Lax434175.ParallelMachines.Environment.uniform

namespace Lax434175.ParallelMachines.Environment.unrelated
end Lax434175.ParallelMachines.Environment.unrelated

namespace Lax434175.ParallelMachines.ProcessingTimes.arbitrary
end Lax434175.ParallelMachines.ProcessingTimes.arbitrary

namespace Lax434175.ParallelMachines.ProcessingTimes.equal
end Lax434175.ParallelMachines.ProcessingTimes.equal

namespace Lax434175.ParallelMachines.ProcessingTimes.holds
end Lax434175.ParallelMachines.ProcessingTimes.holds

namespace Lax434175.ParallelMachines.ProcessingTimes.le
end Lax434175.ParallelMachines.ProcessingTimes.le

namespace Lax434175.ParallelMachines.ProcessingTimes.oneOrTwo
end Lax434175.ParallelMachines.ProcessingTimes.oneOrTwo

namespace Lax434175.ParallelMachines.ProcessingTimes.unit
end Lax434175.ParallelMachines.ProcessingTimes.unit

namespace Lax434175.ParallelMachines

open Lax434175.Kernels Lax434175.Modules

structure Inst where
  jobs : ℕ
  machines : ℕ
  /-- The processing time of a job on a machine. -/
  p : Fin jobs → Fin machines → ℕ
  /-- The release date of a job. -/
  r : Fin jobs → ℕ

end Lax434175.ParallelMachines
end

-- Lax434175.Preemptive
section
namespace Lax434175.Preemptive

open Lax434175.Kernels Lax434175.ParallelMachines

/-- A job is processed on a set of machines from `start` for `length` time
units. -/
structure Piece (x : Inst) where
  job : Fin x.jobs
  machines : Finset (Fin x.machines)
  start : NNRat
  length : NNRat

/-- The time at which a piece ends. -/
def Piece.finish {x : Inst} (q : Piece x) : NNRat := q.start + q.length

structure Sched (x : Inst) where
  pieces : List (Piece x)

/-- The pieces of a job. -/
def piecesOf {x : Inst} (σ : Sched x) (j : Fin x.jobs) : List (Piece x) :=
  σ.pieces.filter (fun q => decide (q.job = j))

/-- The end of the last piece of a job. -/
def completion (x : Inst) (σ : Sched x) (j : Fin x.jobs) : NNRat :=
  (((piecesOf σ j).map Piece.finish).max?).getD 0

end Lax434175.Preemptive
end
