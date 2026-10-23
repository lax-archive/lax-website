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

-- Lax434175.Shops
section
namespace Lax434175.Shops.Machines
end Lax434175.Shops.Machines

namespace Lax434175.Shops.NoWait
end Lax434175.Shops.NoWait

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

inductive ProcessingTimes
  | unit
  | equal
  | arbitrary

/-- The instances of a processing-time restriction. -/
def ProcessingTimes.holds : ProcessingTimes → Inst → Prop
  | .unit, x => ∀ j k, x.p j k = 1
  | .equal, x => ∃ p, ∀ j k, x.p j k = p
  | .arbitrary, _ => True

/-- The position of a value in the chain unit, equal, arbitrary. -/
def ProcessingTimes.rank : ProcessingTimes → ℕ
  | .unit => 0
  | .equal => 1
  | .arbitrary => 2

/-- The processing-time field. -/
def processingTimes : Module kernel :=
  Module.ofRestriction ProcessingTimes ProcessingTimes.holds
    (fun v w => decide (v.rank ≤ w.rank))

axiom processingTimes_sound : processingTimes.Sound

end Lax434175.Shops
end
