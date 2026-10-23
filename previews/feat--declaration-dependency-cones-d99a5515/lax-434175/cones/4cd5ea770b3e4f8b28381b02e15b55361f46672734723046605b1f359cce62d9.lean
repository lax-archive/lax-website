-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

-- Lax434175.ParallelMachines
section
namespace Lax434175.ParallelMachines.ProcessingTimes
end Lax434175.ParallelMachines.ProcessingTimes

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

/-- A kernel on parallel machines. -/
structure Model where
  kernel : Kernel
  /-- The parallel-machine instance underlying an instance of the kernel. -/
  inst : kernel.Inst → Inst
  /-- The jobs of the kernel are those of the underlying instance. -/
  jobs_eq : ∀ x, kernel.jobs x = (inst x).jobs
  /-- At some time of the schedule the job occupies exactly this set of
  machines. -/
  uses : (x : kernel.Inst) → kernel.Sched x → Fin (inst x).jobs →
    Finset (Fin (inst x).machines) → Prop

inductive Environment
  | identical
  | uniform
  | unrelated

/-- The instances of a machine environment. -/
def Environment.holds : Environment → Inst → Prop
  | .identical, x => ∀ j i i', x.p j i = x.p j i'
  | .uniform, x => ∃ (q : Fin x.jobs → ℕ) (s : Fin x.machines → ℕ),
      ∀ j i, 0 < s i ∧ x.p j i * s i = q j
  | .unrelated, _ => True

/-- The position of an environment in the chain identical, uniform, unrelated. -/
def Environment.rank : Environment → ℕ
  | .identical => 0
  | .uniform => 1
  | .unrelated => 2

/-- The machine-environment field. -/
def environment (M : Model) : Module M.kernel :=
  Module.ofRestriction Environment (fun v x => v.holds (M.inst x))
    (fun v w => decide (v.rank ≤ w.rank))

axiom environment_sound (M : Model) : (environment M).Sound

end Lax434175.ParallelMachines
end
