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
namespace Lax434175.Modules.Objective
end Lax434175.Modules.Objective

namespace Lax434175.Modules.Objective.Sound
end Lax434175.Modules.Objective.Sound

namespace Lax434175.Modules

open Lax434175.Kernels

/-- A field whose values add data to an instance and a constraint on its
schedules. -/
structure Module (K : Kernel) where
  Value : Type
  /-- The data a value adds to an instance. -/
  Data : Value → K.Inst → Type
  /-- The condition a value imposes on an instance and its data. -/
  admits : (v : Value) → (x : K.Inst) → Data v x → Prop
  /-- The constraint a value imposes on the schedules. -/
  constraint : (v : Value) → (x : K.Inst) → Data v x → K.Sched x → Prop
  /-- `le v w`: the value `v` is a special case of `w`. -/
  le : Value → Value → Bool
  /-- Data of a value read as data of a more general value. -/
  embed : {v w : Value} → le v w = true → (x : K.Inst) → Data v x → Data w x

/-- Reading data with a more general value keeps it admissible and does not
change the constraint. -/
structure Module.Sound {K : Kernel} (M : Module K) : Prop where
  admits : ∀ (v w : M.Value) (h : M.le v w = true) (x : K.Inst) (d : M.Data v x),
    M.admits v x d → M.admits w x (M.embed h x d)
  constraint : ∀ (v w : M.Value) (h : M.le v w = true) (x : K.Inst) (d : M.Data v x)
    (σ : K.Sched x), M.admits v x d →
      (M.constraint w x (M.embed h x d) σ ↔ M.constraint v x d σ)

/-- A module without data and without a constraint on schedules: each value
only restricts the instances of the kernel. -/
def Module.ofRestriction {K : Kernel} (Value : Type) (holds : Value → K.Inst → Prop)
    (le : Value → Value → Bool) : Module K where
  Value := Value
  Data _ _ := Unit
  admits v x _ := holds v x
  constraint _ _ _ _ := True
  le := le
  embed _ _ _ := ()

end Lax434175.Modules
end

-- Lax434175.Batching
section
namespace Lax434175.Batching.Capacity
end Lax434175.Batching.Capacity

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

inductive ProcessingTimes
  | unit
  | equal
  | arbitrary

/-- The instances of a processing-time restriction. -/
def ProcessingTimes.holds : ProcessingTimes → Inst → Prop
  | .unit, x => ∀ j, x.p j = 1
  | .equal, x => ∃ p, ∀ j, x.p j = p
  | .arbitrary, _ => True

/-- The position of a value in the chain unit, equal, arbitrary. -/
def ProcessingTimes.rank : ProcessingTimes → ℕ
  | .unit => 0
  | .equal => 1
  | .arbitrary => 2

/-- The processing-time field. -/
def processingTimes (mode : Mode) : Module (kernel mode) :=
  Module.ofRestriction ProcessingTimes ProcessingTimes.holds
    (fun v w => decide (v.rank ≤ w.rank))

axiom processingTimes_sound (mode : Mode) : (processingTimes mode).Sound

end Lax434175.Batching
end
