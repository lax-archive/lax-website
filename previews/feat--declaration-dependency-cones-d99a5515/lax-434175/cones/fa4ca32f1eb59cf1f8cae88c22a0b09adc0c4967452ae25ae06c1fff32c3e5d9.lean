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

/-- In every schedule that is feasible for the kernel, every job starts no
later than it completes. -/
def Kernel.StartsBeforeCompletion (K : Kernel) : Prop :=
  ∀ x (σ : K.Sched x), K.feasible x σ → ∀ j, K.start x σ j ≤ K.completion x σ j

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

/-- Two pieces do not overlap in time. -/
def Apart {x : Inst} (a b : Piece x) : Prop :=
  a.finish ≤ b.start ∨ b.finish ≤ a.start

/-- The start of the first piece of a job. -/
def start (x : Inst) (σ : Sched x) (j : Fin x.jobs) : NNRat :=
  (((piecesOf σ j).map Piece.start).min?).getD 0

/-- The end of the last piece of a job. -/
def completion (x : Inst) (σ : Sched x) (j : Fin x.jobs) : NNRat :=
  (((piecesOf σ j).map Piece.finish).max?).getD 0

end Lax434175.Preemptive
end

-- Lax434175.Restarts
section
namespace Lax434175.Restarts
end Lax434175.Restarts
end

-- Lax434175.Interruption
section
namespace Lax434175.Interruption.Mode
end Lax434175.Interruption.Mode

namespace Lax434175.Interruption.Mode.holds
end Lax434175.Interruption.Mode.holds

namespace Lax434175.Interruption.Mode.none
end Lax434175.Interruption.Mode.none

namespace Lax434175.Interruption.Mode.pmtn
end Lax434175.Interruption.Mode.pmtn

namespace Lax434175.Interruption.Mode.pmtnNoMigration
end Lax434175.Interruption.Mode.pmtnNoMigration

namespace Lax434175.Interruption.Mode.restarts
end Lax434175.Interruption.Mode.restarts

namespace Lax434175.Interruption

open Lax434175.Kernels Lax434175.Modules Lax434175.ParallelMachines Lax434175.Preemptive

/-- Every piece occupies some machine, and two different pieces that share a
machine or a job do not overlap. -/
def feasible {x : Inst} (σ : Sched x) : Prop :=
  (∀ q ∈ σ.pieces, q.machines.Nonempty) ∧
  σ.pieces.Pairwise (fun a b => (¬ Disjoint a.machines b.machines ∨ a.job = b.job) → Apart a b)

/-- The kernel of scheduling on parallel machines with pieces. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible _ σ := feasible σ
  start := start
  completion := completion

axiom startsBeforeCompletion : kernel.StartsBeforeCompletion

end Lax434175.Interruption
end
