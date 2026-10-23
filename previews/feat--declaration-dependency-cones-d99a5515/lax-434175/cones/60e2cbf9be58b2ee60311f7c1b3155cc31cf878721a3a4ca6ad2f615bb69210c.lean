-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Rat
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
namespace Lax434175.Shops.NoWait
end Lax434175.Shops.NoWait

namespace Lax434175.Shops.ProcessingTimes
end Lax434175.Shops.ProcessingTimes

namespace Lax434175.Shops.Sched
end Lax434175.Shops.Sched

namespace Lax434175.Shops.ShopType
end Lax434175.Shops.ShopType

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

inductive Machines
  | byPosition
  | dedicated
  | recirculation
  | stages
  | sets
  | fix
  | general

/-- The data of a value of the machine field. -/
def Machines.Data : Machines → Inst → Type
  | .byPosition, _ | .stages, _ => Unit
  | .dedicated, x | .recirculation, x => (j : Fin x.jobs) → Fin (x.ops j) → ℕ
  | .sets, x => (j : Fin x.jobs) → Fin (x.ops j) → Fin x.machines → Prop
  | .fix, x => (j : Fin x.jobs) → Fin (x.ops j) → Finset (Fin x.machines)
  | .general, x => (j : Fin x.jobs) → Fin (x.ops j) → Finset (Fin x.machines) → Prop

/-- The set consisting of the machine with a given number. Machines are
numbered from `0`. -/
def machineNumbered (x : Inst) (i : ℕ) : Finset (Fin x.machines) :=
  Finset.univ.filter (fun i' => i'.val = i)

/-- Whether an operation may occupy a set of machines. -/
def Machines.view {x : Inst} : (v : Machines) → v.Data x →
    (j : Fin x.jobs) → Fin (x.ops j) → Finset (Fin x.machines) → Prop
  | .byPosition, _ => fun _ k S => S = machineNumbered x k.val
  | .dedicated, μ | .recirculation, μ => fun j k S => S = machineNumbered x (μ j k)
  | .stages, _ => fun _ k S =>
      (k.val = 0 → S = machineNumbered x 0) ∧ (k.val ≠ 0 → S.card = 1 ∧ ∀ i ∈ S, i.val ≠ 0)
  | .sets, M => fun j k S => S.card = 1 ∧ ∀ i ∈ S, M j k i
  | .fix, F => fun j k S => S = F j k
  | .general, allowed => allowed

/-- The condition on the data: a given machine number is the number of a
machine, and with dedicated machines no two operations of a job are given
the same machine. -/
def Machines.admits {x : Inst} : (v : Machines) → v.Data x → Prop
  | .byPosition, _ => ∀ j (k : Fin (x.ops j)), k.val < x.machines
  | .dedicated, μ => (∀ j k, μ j k < x.machines) ∧ ∀ j k k', μ j k = μ j k' → k = k'
  | .recirculation, μ => ∀ j k, μ j k < x.machines
  | .stages, _ => 0 < x.machines
  | _, _ => True

def Machines.le : Machines → Machines → Bool
  | .byPosition, .stages | .dedicated, .stages | .recirculation, .stages => false
  | .byPosition, _ => true
  | .dedicated, .byPosition => false
  | .dedicated, _ => true
  | .recirculation, .byPosition | .recirculation, .dedicated => false
  | .recirculation, _ => true
  | .stages, .stages | .stages, .sets | .stages, .general => true
  | .sets, .sets | .sets, .general => true
  | .fix, .fix | .fix, .general => true
  | .general, .general => true
  | _, _ => false

def Machines.embed : {v w : Machines} → Machines.le v w = true → (x : Inst) →
    v.Data x → w.Data x
  | .byPosition, .byPosition, _, _, _ => ()
  | .byPosition, .dedicated, _, _, _ | .byPosition, .recirculation, _, _, _ =>
      fun _ k => k.val
  | .byPosition, .sets, _, _, _ => fun _ k i => i.val = k.val
  | .byPosition, .fix, _, x, _ => fun _ k => machineNumbered x k.val
  | .dedicated, .dedicated, _, _, μ | .dedicated, .recirculation, _, _, μ
  | .recirculation, .recirculation, _, _, μ => μ
  | .dedicated, .sets, _, _, μ | .recirculation, .sets, _, _, μ => fun j k i => i.val = μ j k
  | .dedicated, .fix, _, x, μ | .recirculation, .fix, _, x, μ =>
      fun j k => machineNumbered x (μ j k)
  | .stages, .stages, _, _, _ => ()
  | .stages, .sets, _, _, _ => fun _ k i => (k.val = 0 ∧ i.val = 0) ∨ (k.val ≠ 0 ∧ i.val ≠ 0)
  | .sets, .sets, _, _, d => d
  | .fix, .fix, _, _, d => d
  | v, .general, _, _, d => v.view d
  | .byPosition, .stages, h, _, _ | .dedicated, .stages, h, _, _
  | .recirculation, .stages, h, _, _ | .sets, .stages, h, _, _ | .fix, .stages, h, _, _
  | .general, .stages, h, _, _ | .stages, .byPosition, h, _, _ | .stages, .dedicated, h, _, _
  | .stages, .recirculation, h, _, _ | .stages, .fix, h, _, _
  | .dedicated, .byPosition, h, _, _
  | .recirculation, .byPosition, h, _, _ | .recirculation, .dedicated, h, _, _
  | .sets, .byPosition, h, _, _ | .sets, .dedicated, h, _, _
  | .sets, .recirculation, h, _, _ | .sets, .fix, h, _, _ | .fix, .byPosition, h, _, _
  | .fix, .dedicated, h, _, _ | .fix, .recirculation, h, _, _ | .fix, .sets, h, _, _
  | .general, .byPosition, h, _, _ | .general, .dedicated, h, _, _
  | .general, .recirculation, h, _, _ | .general, .sets, h, _, _ | .general, .fix, h, _, _ =>
      absurd h Bool.false_ne_true

end Lax434175.Shops
end

-- Lax434175.PreemptiveShops
section
namespace Lax434175.PreemptiveShops.ordered
end Lax434175.PreemptiveShops.ordered

namespace Lax434175.PreemptiveShops

open Lax434175.Kernels Lax434175.Modules Lax434175.Shops

/-- An operation is processed on a set of machines from `start` for `length`
time units. -/
structure Piece (x : Inst) where
  op : Op x
  machines : Finset (Fin x.machines)
  start : NNRat
  length : NNRat

/-- The time at which a piece ends. -/
def Piece.finish {x : Inst} (q : Piece x) : NNRat := q.start + q.length

structure Sched (x : Inst) where
  pieces : List (Piece x)

/-- The pieces of an operation. -/
def piecesOf {x : Inst} (σ : Sched x) (o : Op x) : List (Piece x) :=
  σ.pieces.filter (fun q => decide (q.op = o))

/-- The pieces of a job. -/
def piecesOfJob {x : Inst} (σ : Sched x) (j : Fin x.jobs) : List (Piece x) :=
  σ.pieces.filter (fun q => decide (q.op.1 = j))

/-- Two pieces do not overlap in time. -/
def Apart {x : Inst} (a b : Piece x) : Prop :=
  a.finish ≤ b.start ∨ b.finish ≤ a.start

def feasible (x : Inst) (σ : Sched x) : Prop :=
  (∀ q ∈ σ.pieces, q.machines.Nonempty) ∧
  σ.pieces.Pairwise
    (fun a b => (a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) → Apart a b) ∧
  ∀ o : Op x, ((piecesOf σ o).map fun q => q.length / (x.p o.1 o.2 : NNRat)).sum = 1 ∨
    ∃ q ∈ piecesOf σ o, x.p o.1 o.2 = 0

/-- The kernel of preemptive shop scheduling. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible := feasible
  start _ σ j := (((piecesOfJob σ j).map Piece.start).min?).getD 0
  completion _ σ j := (((piecesOfJob σ j).map Piece.finish).max?).getD 0

/-- The machine field. -/
def machineSets : Module kernel where
  Value := Machines
  Data := Machines.Data
  admits v _ d := v.admits d
  constraint v _ d σ := ∀ q ∈ Sched.pieces σ, v.view d q.op.1 q.op.2 q.machines
  le := Machines.le
  embed := Machines.embed

end Lax434175.PreemptiveShops
end
