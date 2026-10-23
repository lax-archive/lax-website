-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
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

namespace Lax434175.Modules.Module.Sound
end Lax434175.Modules.Module.Sound

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

end Lax434175.Modules
end

-- Lax434175.Shops
section
namespace Lax434175.Shops.Machines
end Lax434175.Shops.Machines

namespace Lax434175.Shops.NoWait
end Lax434175.Shops.NoWait

namespace Lax434175.Shops.ProcessingTimes
end Lax434175.Shops.ProcessingTimes

namespace Lax434175.Shops.ShopType
end Lax434175.Shops.ShopType

namespace Lax434175.Shops.Machines.Data
end Lax434175.Shops.Machines.Data

namespace Lax434175.Shops.Machines.admits
end Lax434175.Shops.Machines.admits

namespace Lax434175.Shops.Machines.byPosition
end Lax434175.Shops.Machines.byPosition

namespace Lax434175.Shops.Machines.dedicated
end Lax434175.Shops.Machines.dedicated

namespace Lax434175.Shops.Machines.embed
end Lax434175.Shops.Machines.embed

namespace Lax434175.Shops.Machines.fix
end Lax434175.Shops.Machines.fix

namespace Lax434175.Shops.Machines.general
end Lax434175.Shops.Machines.general

namespace Lax434175.Shops.Machines.le
end Lax434175.Shops.Machines.le

namespace Lax434175.Shops.Machines.recirculation
end Lax434175.Shops.Machines.recirculation

namespace Lax434175.Shops.Machines.sets
end Lax434175.Shops.Machines.sets

namespace Lax434175.Shops.Machines.stages
end Lax434175.Shops.Machines.stages

namespace Lax434175.Shops.Machines.view
end Lax434175.Shops.Machines.view

namespace Lax434175.Shops.NoWait.constraint
end Lax434175.Shops.NoWait.constraint

namespace Lax434175.Shops.NoWait.noWait
end Lax434175.Shops.NoWait.noWait

namespace Lax434175.Shops.NoWait.none
end Lax434175.Shops.NoWait.none

namespace Lax434175.Shops.ProcessingTimes.arbitrary
end Lax434175.Shops.ProcessingTimes.arbitrary

namespace Lax434175.Shops.ProcessingTimes.equal
end Lax434175.Shops.ProcessingTimes.equal

namespace Lax434175.Shops.ProcessingTimes.holds
end Lax434175.Shops.ProcessingTimes.holds

namespace Lax434175.Shops.ProcessingTimes.rank
end Lax434175.Shops.ProcessingTimes.rank

namespace Lax434175.Shops.ProcessingTimes.unit
end Lax434175.Shops.ProcessingTimes.unit

namespace Lax434175.Shops.ShopType.flexibleFlow
end Lax434175.Shops.ShopType.flexibleFlow

namespace Lax434175.Shops.ShopType.flow
end Lax434175.Shops.ShopType.flow

namespace Lax434175.Shops.ShopType.holds
end Lax434175.Shops.ShopType.holds

namespace Lax434175.Shops.ShopType.job
end Lax434175.Shops.ShopType.job

namespace Lax434175.Shops.ShopType.le
end Lax434175.Shops.ShopType.le

namespace Lax434175.Shops.ShopType.open
end Lax434175.Shops.ShopType.open

namespace Lax434175.Shops.ShopType.ordered
end Lax434175.Shops.ShopType.ordered

namespace Lax434175.Shops

open Lax434175.Kernels Lax434175.Modules

structure Inst where
  jobs : ℕ
  machines : ℕ
  /-- The number of operations of a job. -/
  ops : Fin jobs → ℕ
  /-- The processing time of an operation. -/
  p : (j : Fin jobs) → Fin (ops j) → ℕ
  /-- The release date of a job. -/
  r : Fin jobs → ℕ

/-- An operation: a job and a position in its sequence. -/
abbrev Op (x : Inst) := (j : Fin x.jobs) × Fin (x.ops j)

structure Sched (x : Inst) where
  machines : (j : Fin x.jobs) → Fin (x.ops j) → Finset (Fin x.machines)
  start : (j : Fin x.jobs) → Fin (x.ops j) → ℕ

/-- The time at which an operation completes. -/
def finish (x : Inst) (σ : Sched x) (o : Op x) : ℕ :=
  σ.start o.1 o.2 + x.p o.1 o.2

/-- Every operation occupies some machine, and two different operations of
the same job or sharing a machine do not overlap. -/
def feasible (x : Inst) (σ : Sched x) : Prop :=
  (∀ o : Op x, (σ.machines o.1 o.2).Nonempty) ∧
  ∀ a b : Op x, a ≠ b →
    (a.1 = b.1 ∨ ¬ Disjoint (σ.machines a.1 a.2) (σ.machines b.1 b.2)) →
    finish x σ a ≤ σ.start b.1 b.2 ∨ finish x σ b ≤ σ.start a.1 a.2

/-- The start of the first operation of a job. -/
def jobStart (x : Inst) (σ : Sched x) (j : Fin x.jobs) : ℕ :=
  ((List.ofFn (σ.start j)).min?).getD 0

/-- The completion of the last operation of a job. -/
def jobCompletion (x : Inst) (σ : Sched x) (j : Fin x.jobs) : ℕ :=
  ((List.ofFn (fun k => finish x σ ⟨j, k⟩)).max?).getD 0

/-- The kernel of non-preemptive shop scheduling. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible := feasible
  start x σ j := (jobStart x σ j : NNRat)
  completion x σ j := (jobCompletion x σ j : NNRat)

end Lax434175.Shops
end

-- Lax434175.ShopExtras
section
namespace Lax434175.ShopExtras.NoIdle
end Lax434175.ShopExtras.NoIdle

namespace Lax434175.ShopExtras.NoIdle.noIdle
end Lax434175.ShopExtras.NoIdle.noIdle

namespace Lax434175.ShopExtras.NoIdle.none
end Lax434175.ShopExtras.NoIdle.none

namespace Lax434175.ShopExtras

open Lax434175.Kernels Lax434175.Modules Lax434175.Shops

/-- An operation occupies a machine. -/
def Occupies {x : Inst} (σ : Sched x) (o : Op x) (i : Fin x.machines) : Prop :=
  i ∈ σ.machines o.1 o.2

inductive BatchSetups
  | none
  | batchSetups

/-- The data of a value: the batch of every job and the setup times between
batches. -/
def BatchSetups.Data : BatchSetups → Inst → Type
  | .none, _ => Unit
  | .batchSetups, x => (Fin x.jobs → ℕ) × (ℕ → ℕ → ℕ)

/-- The batch of a job; a single batch when the field is absent. -/
def BatchSetups.batch {x : Inst} : (v : BatchSetups) → v.Data x → Fin x.jobs → ℕ
  | .none, _ => fun _ => 0
  | .batchSetups, d => d.1

/-- The setup time between two batches. -/
def BatchSetups.setup {x : Inst} : (v : BatchSetups) → v.Data x → ℕ → ℕ → ℕ
  | .none, _ => fun _ _ => 0
  | .batchSetups, d => d.2

def BatchSetups.le : BatchSetups → BatchSetups → Bool
  | .batchSetups, .none => false
  | _, _ => true

def BatchSetups.embed : {v w : BatchSetups} → BatchSetups.le v w = true → (x : Inst) →
    v.Data x → w.Data x
  | _, .none, _, _, _ => ()
  | v, .batchSetups, _, _, d => (v.batch d, v.setup d)

/-- On some machine, operation `b` follows operation `a`: `b` starts after `a`
completes, and no other operation on that machine lies in between. -/
def Follows {x : Inst} (σ : Sched x) (a b : Op x) : Prop :=
  finish x σ a ≤ σ.start b.1 b.2 ∧ ∃ i, Occupies σ a i ∧ Occupies σ b i ∧
    ∀ c : Op x, c ≠ a → c ≠ b → Occupies σ c i →
      ¬ (finish x σ a ≤ σ.start c.1 c.2 ∧ finish x σ c ≤ σ.start b.1 b.2)

/-- The batch-setup field. -/
def batchSetups : Module kernel where
  Value := BatchSetups
  Data := BatchSetups.Data
  admits _ _ _ := True
  constraint v x d σ := ∀ a b : Op x, v.batch d a.1 ≠ v.batch d b.1 →
    (¬ Disjoint (σ.machines a.1 a.2) (σ.machines b.1 b.2) →
      finish x σ a ≤ σ.start b.1 b.2 ∨ finish x σ b ≤ σ.start a.1 a.2) ∧
    (Follows σ a b → finish x σ a + v.setup d (v.batch d a.1) (v.batch d b.1) ≤ σ.start b.1 b.2)
  le := BatchSetups.le
  embed := BatchSetups.embed

end Lax434175.ShopExtras
end
