-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
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

-- Lax434175.Batching
section
namespace Lax434175.Batching.Capacity
end Lax434175.Batching.Capacity

namespace Lax434175.Batching.ProcessingTimes
end Lax434175.Batching.ProcessingTimes

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

inductive Mode
  | serial
  | parallel

structure Sched (x : Inst) where
  /-- The number of the batch of a job. -/
  batch : Fin x.jobs → ℕ
  /-- The start time of a batch. -/
  start : ℕ → ℕ

/-- The jobs of a batch. -/
def members {x : Inst} (σ : Sched x) (k : ℕ) : Finset (Fin x.jobs) :=
  Finset.univ.filter (fun j => σ.batch j = k)

/-- The processing time of a batch. -/
def length (mode : Mode) (x : Inst) (σ : Sched x) (k : ℕ) : ℕ :=
  match mode with
  | .serial => ∑ j ∈ members σ k, x.p j
  | .parallel => (members σ k).sup x.p

/-- The completion time of a batch. -/
def finish (mode : Mode) (x : Inst) (σ : Sched x) (k : ℕ) : ℕ :=
  σ.start k + length mode x σ k

/-- A setup precedes every batch. -/
def feasible (mode : Mode) (x : Inst) (σ : Sched x) : Prop :=
  (∀ j, x.setup ≤ σ.start (σ.batch j)) ∧
  ∀ i j, σ.batch i < σ.batch j →
    finish mode x σ (σ.batch i) + x.setup ≤ σ.start (σ.batch j)

/-- The kernel of batch scheduling in a mode. -/
def kernel (mode : Mode) : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible := feasible mode
  start _ σ j := (σ.start (σ.batch j) : NNRat)
  completion x σ j := (finish mode x σ (σ.batch j) : NNRat)

end Lax434175.Batching
end
