-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.NNRat.Defs
import Mathlib.Logic.Relation

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

end Lax434175.Modules
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
end Lax434175.Preemptive

namespace Lax434175.Preemptive.Piece
end Lax434175.Preemptive.Piece

namespace Lax434175.Preemptive.Sched
end Lax434175.Preemptive.Sched
end

-- Lax434175.Restarts
section
namespace Lax434175.Restarts
end Lax434175.Restarts
end

-- Lax434175.Interruption
section
namespace Lax434175.Interruption
end Lax434175.Interruption

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
end

-- Lax434175.MachineSets
section
namespace Lax434175.MachineSets

open Lax434175.Kernels Lax434175.Modules Lax434175.ParallelMachines

inductive Value
  | none
  | sets
  | fix
  | sizeOneOrAll
  | size
  | general

/-- The data of a value. -/
def Data : Value → Inst → Type
  | .none, _ => Unit
  | .sets, x => Fin x.jobs → Fin x.machines → Prop
  | .fix, x => Fin x.jobs → Finset (Fin x.machines)
  | .sizeOneOrAll, x => Fin x.jobs → Bool
  | .size, x => Fin x.jobs → ℕ
  | .general, x => Fin x.jobs → Finset (Fin x.machines) → Prop

/-- Whether a job may occupy a set of machines. -/
def view {x : Inst} : (v : Value) → Data v x → Fin x.jobs → Finset (Fin x.machines) → Prop
  | .none, _ => fun _ S => S.card = 1
  | .sets, M => fun j S => S.card = 1 ∧ ∀ i ∈ S, M j i
  | .fix, F => fun j S => S = F j
  | .sizeOneOrAll, all => fun j S => S.card = if all j then x.machines else 1
  | .size, size => fun j S => S.card = size j
  | .general, allowed => allowed

def le : Value → Value → Bool
  | .none, .fix => false
  | .none, _ => true
  | .sets, .sets | .sets, .general => true
  | .fix, .fix | .fix, .general => true
  | .sizeOneOrAll, .sizeOneOrAll | .sizeOneOrAll, .size | .sizeOneOrAll, .general => true
  | .size, .size | .size, .general => true
  | .general, .general => true
  | _, _ => false

def embed : {v w : Value} → le v w = true → (x : Inst) → Data v x → Data w x
  | .none, .none, _, _, _ => ()
  | .none, .sets, _, _, _ => fun _ _ => True
  | .none, .sizeOneOrAll, _, _, _ => fun _ => false
  | .none, .size, _, _, _ => fun _ => 1
  | .sets, .sets, _, _, d => d
  | .fix, .fix, _, _, d => d
  | .sizeOneOrAll, .sizeOneOrAll, _, _, d => d
  | .sizeOneOrAll, .size, _, x, d => fun j => if d j then x.machines else 1
  | .size, .size, _, _, d => d
  | v, .general, _, _, d => view v d
  | .none, .fix, h, _, _ | .sets, .none, h, _, _ | .sets, .fix, h, _, _
  | .sets, .sizeOneOrAll, h, _, _ | .sets, .size, h, _, _ | .fix, .none, h, _, _
  | .fix, .sets, h, _, _ | .fix, .sizeOneOrAll, h, _, _ | .fix, .size, h, _, _
  | .sizeOneOrAll, .none, h, _, _ | .sizeOneOrAll, .sets, h, _, _
  | .sizeOneOrAll, .fix, h, _, _ | .size, .none, h, _, _ | .size, .sets, h, _, _
  | .size, .fix, h, _, _ | .size, .sizeOneOrAll, h, _, _ | .general, .none, h, _, _
  | .general, .sets, h, _, _ | .general, .fix, h, _, _ | .general, .sizeOneOrAll, h, _, _
  | .general, .size, h, _, _ => absurd h Bool.false_ne_true

end Lax434175.MachineSets
end

-- Lax434175.Problems
section
namespace Lax434175
end Lax434175

namespace Lax434175.Problems
end Lax434175.Problems

namespace Lax434175.Problems.DecisionReduction
end Lax434175.Problems.DecisionReduction

namespace Lax434175.Problems.Embedding
end Lax434175.Problems.Embedding

namespace Lax434175.Problems.Problem
end Lax434175.Problems.Problem

namespace Lax434175.Problems.Embedding.Sound
end Lax434175.Problems.Embedding.Sound
end

-- Lax434175.Assembly
section
namespace Lax434175.Assembly
end Lax434175.Assembly

namespace Lax434175.Assembly.Family
end Lax434175.Assembly.Family

namespace Lax434175.Assembly.Inst
end Lax434175.Assembly.Inst

namespace Lax434175.Assembly.Spec
end Lax434175.Assembly.Spec

namespace Lax434175.Assembly.Family.Sound
end Lax434175.Assembly.Family.Sound
end

-- Lax434175.Counts
section
namespace Lax434175.Counts
end Lax434175.Counts

namespace Lax434175.Counts.Bound
end Lax434175.Counts.Bound

namespace Lax434175.Counts.Bound.any
end Lax434175.Counts.Bound.any

namespace Lax434175.Counts.Bound.atMost
end Lax434175.Counts.Bound.atMost

namespace Lax434175.Counts.Bound.atMostJobsPlusOne
end Lax434175.Counts.Bound.atMostJobsPlusOne

namespace Lax434175.Counts.Bound.constant
end Lax434175.Counts.Bound.constant

namespace Lax434175.Counts.Bound.holds
end Lax434175.Counts.Bound.holds

namespace Lax434175.Counts.Bound.le
end Lax434175.Counts.Bound.le

namespace Lax434175.Counts.Bound.unlimited
end Lax434175.Counts.Bound.unlimited
end

-- Lax434175.Deadlines
section
namespace Lax434175.Deadlines
end Lax434175.Deadlines

namespace Lax434175.Deadlines.Data
end Lax434175.Deadlines.Data

namespace Lax434175.Deadlines.Value
end Lax434175.Deadlines.Value

namespace Lax434175.Deadlines.Within
end Lax434175.Deadlines.Within

namespace Lax434175.Deadlines.embed
end Lax434175.Deadlines.embed

namespace Lax434175.Deadlines.le
end Lax434175.Deadlines.le

namespace Lax434175.Deadlines.view
end Lax434175.Deadlines.view

namespace Lax434175.Deadlines.Value.common
end Lax434175.Deadlines.Value.common

namespace Lax434175.Deadlines.Value.deadlines
end Lax434175.Deadlines.Value.deadlines

namespace Lax434175.Deadlines.Value.none
end Lax434175.Deadlines.Value.none
end

-- Lax434175.Precedence
section
namespace Lax434175.Precedence
end Lax434175.Precedence

namespace Lax434175.Precedence.DivideAndConquer
end Lax434175.Precedence.DivideAndConquer

namespace Lax434175.Precedence.HasPath
end Lax434175.Precedence.HasPath

namespace Lax434175.Precedence.Lags
end Lax434175.Precedence.Lags

namespace Lax434175.Precedence.Order
end Lax434175.Precedence.Order

namespace Lax434175.Precedence.Value
end Lax434175.Precedence.Value

namespace Lax434175.Precedence.Lags.Admits
end Lax434175.Precedence.Lags.Admits

namespace Lax434175.Precedence.Lags.Data
end Lax434175.Precedence.Lags.Data

namespace Lax434175.Precedence.Lags.arbitrary
end Lax434175.Precedence.Lags.arbitrary

namespace Lax434175.Precedence.Lags.arbitraryNonpositive
end Lax434175.Precedence.Lags.arbitraryNonpositive

namespace Lax434175.Precedence.Lags.arbitraryPositive
end Lax434175.Precedence.Lags.arbitraryPositive

namespace Lax434175.Precedence.Lags.constant
end Lax434175.Precedence.Lags.constant

namespace Lax434175.Precedence.Lags.constantNonpositive
end Lax434175.Precedence.Lags.constantNonpositive

namespace Lax434175.Precedence.Lags.constantPositive
end Lax434175.Precedence.Lags.constantPositive

namespace Lax434175.Precedence.Lags.embed
end Lax434175.Precedence.Lags.embed

namespace Lax434175.Precedence.Lags.le
end Lax434175.Precedence.Lags.le

namespace Lax434175.Precedence.Lags.unit
end Lax434175.Precedence.Lags.unit

namespace Lax434175.Precedence.Lags.view
end Lax434175.Precedence.Lags.view

namespace Lax434175.Precedence.Lags.zero
end Lax434175.Precedence.Lags.zero

namespace Lax434175.Precedence.Order.Data
end Lax434175.Precedence.Order.Data

namespace Lax434175.Precedence.Order.InClass
end Lax434175.Precedence.Order.InClass

namespace Lax434175.Precedence.Order.aOrder
end Lax434175.Precedence.Order.aOrder

namespace Lax434175.Precedence.Order.boundedDimension
end Lax434175.Precedence.Order.boundedDimension

namespace Lax434175.Precedence.Order.boundedHeight
end Lax434175.Precedence.Order.boundedHeight

namespace Lax434175.Precedence.Order.chains
end Lax434175.Precedence.Order.chains

namespace Lax434175.Precedence.Order.dimensionTwo
end Lax434175.Precedence.Order.dimensionTwo

namespace Lax434175.Precedence.Order.divideAndConquer
end Lax434175.Precedence.Order.divideAndConquer

namespace Lax434175.Precedence.Order.embed
end Lax434175.Precedence.Order.embed

namespace Lax434175.Precedence.Order.intervalOrder
end Lax434175.Precedence.Order.intervalOrder

namespace Lax434175.Precedence.Order.intree
end Lax434175.Precedence.Order.intree

namespace Lax434175.Precedence.Order.le
end Lax434175.Precedence.Order.le

namespace Lax434175.Precedence.Order.levelOrder
end Lax434175.Precedence.Order.levelOrder

namespace Lax434175.Precedence.Order.none
end Lax434175.Precedence.Order.none

namespace Lax434175.Precedence.Order.opposingForest
end Lax434175.Precedence.Order.opposingForest

namespace Lax434175.Precedence.Order.outtree
end Lax434175.Precedence.Order.outtree

namespace Lax434175.Precedence.Order.overInterval
end Lax434175.Precedence.Order.overInterval

namespace Lax434175.Precedence.Order.prec
end Lax434175.Precedence.Order.prec

namespace Lax434175.Precedence.Order.quasiInterval
end Lax434175.Precedence.Order.quasiInterval

namespace Lax434175.Precedence.Order.seriesParallel
end Lax434175.Precedence.Order.seriesParallel

namespace Lax434175.Precedence.Order.tree
end Lax434175.Precedence.Order.tree

namespace Lax434175.Precedence.Order.view
end Lax434175.Precedence.Order.view
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
namespace Lax434175.PreemptiveShops
end Lax434175.PreemptiveShops

namespace Lax434175.PreemptiveShops.Piece
end Lax434175.PreemptiveShops.Piece

namespace Lax434175.PreemptiveShops.Sched
end Lax434175.PreemptiveShops.Sched

namespace Lax434175.PreemptiveShops.ordered
end Lax434175.PreemptiveShops.ordered
end

-- Lax434175.ReleaseDates
section
namespace Lax434175.ReleaseDates
end Lax434175.ReleaseDates

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
end

-- Lax434175.Objectives
section
namespace Lax434175.Objectives
end Lax434175.Objectives

namespace Lax434175.Objectives.Data
end Lax434175.Objectives.Data

namespace Lax434175.Objectives.Kind
end Lax434175.Objectives.Kind

namespace Lax434175.Objectives.Value
end Lax434175.Objectives.Value

namespace Lax434175.Objectives.admits
end Lax434175.Objectives.admits

namespace Lax434175.Objectives.cost
end Lax434175.Objectives.cost

namespace Lax434175.Objectives.dueDate
end Lax434175.Objectives.dueDate

namespace Lax434175.Objectives.embed
end Lax434175.Objectives.embed

namespace Lax434175.Objectives.hasDueDates
end Lax434175.Objectives.hasDueDates

namespace Lax434175.Objectives.kind
end Lax434175.Objectives.kind

namespace Lax434175.Objectives.restrictionLe
end Lax434175.Objectives.restrictionLe

namespace Lax434175.Objectives.weight
end Lax434175.Objectives.weight

namespace Lax434175.Objectives.weighted
end Lax434175.Objectives.weighted

namespace Lax434175.Objectives.Kind.flow
end Lax434175.Objectives.Kind.flow

namespace Lax434175.Objectives.Kind.late
end Lax434175.Objectives.Kind.late

namespace Lax434175.Objectives.Kind.maximum
end Lax434175.Objectives.Kind.maximum

namespace Lax434175.Objectives.Kind.maximumFlow
end Lax434175.Objectives.Kind.maximumFlow

namespace Lax434175.Objectives.Kind.notJustInTime
end Lax434175.Objectives.Kind.notJustInTime

namespace Lax434175.Objectives.Kind.tardiness
end Lax434175.Objectives.Kind.tardiness

namespace Lax434175.Objectives.Value.fmax
end Lax434175.Objectives.Value.fmax

namespace Lax434175.Objectives.Value.lmax
end Lax434175.Objectives.Value.lmax

namespace Lax434175.Objectives.Value.makespan
end Lax434175.Objectives.Value.makespan

namespace Lax434175.Objectives.Value.maxWF
end Lax434175.Objectives.Value.maxWF

namespace Lax434175.Objectives.Value.sumC
end Lax434175.Objectives.Value.sumC

namespace Lax434175.Objectives.Value.sumF
end Lax434175.Objectives.Value.sumF

namespace Lax434175.Objectives.Value.sumT
end Lax434175.Objectives.Value.sumT

namespace Lax434175.Objectives.Value.sumU
end Lax434175.Objectives.Value.sumU

namespace Lax434175.Objectives.Value.sumWC
end Lax434175.Objectives.Value.sumWC

namespace Lax434175.Objectives.Value.sumWF
end Lax434175.Objectives.Value.sumWF

namespace Lax434175.Objectives.Value.sumWT
end Lax434175.Objectives.Value.sumWT

namespace Lax434175.Objectives.Value.sumWTCommon
end Lax434175.Objectives.Value.sumWTCommon

namespace Lax434175.Objectives.Value.sumWU
end Lax434175.Objectives.Value.sumWU

namespace Lax434175.Objectives.Value.sumWUWindow
end Lax434175.Objectives.Value.sumWUWindow

namespace Lax434175.Objectives.Value.sumWZ
end Lax434175.Objectives.Value.sumWZ

namespace Lax434175.Objectives.Value.sumZ
end Lax434175.Objectives.Value.sumZ
end

-- Lax434175.Parameters
section
namespace Lax434175.Parameters
end Lax434175.Parameters

namespace Lax434175.Parameters.FieldParameter
end Lax434175.Parameters.FieldParameter

namespace Lax434175.Parameters.InPlace
end Lax434175.Parameters.InPlace
end

-- Lax434175.Thresholds
section
namespace Lax434175.Thresholds
end Lax434175.Thresholds
end

-- Lax434175.PreemptiveShopProblems
section
namespace Lax434175.PreemptiveShopProblems
end Lax434175.PreemptiveShopProblems

namespace Lax434175.PreemptiveShopProblems.FieldName
end Lax434175.PreemptiveShopProblems.FieldName

namespace Lax434175.PreemptiveShopProblems.family
end Lax434175.PreemptiveShopProblems.family

namespace Lax434175.PreemptiveShopProblems.spec
end Lax434175.PreemptiveShopProblems.spec

namespace Lax434175.PreemptiveShopProblems.FieldName.deadlines
end Lax434175.PreemptiveShopProblems.FieldName.deadlines

namespace Lax434175.PreemptiveShopProblems.FieldName.jobCount
end Lax434175.PreemptiveShopProblems.FieldName.jobCount

namespace Lax434175.PreemptiveShopProblems.FieldName.machineCount
end Lax434175.PreemptiveShopProblems.FieldName.machineCount

namespace Lax434175.PreemptiveShopProblems.FieldName.machineSets
end Lax434175.PreemptiveShopProblems.FieldName.machineSets

namespace Lax434175.PreemptiveShopProblems.FieldName.precedence
end Lax434175.PreemptiveShopProblems.FieldName.precedence

namespace Lax434175.PreemptiveShopProblems.FieldName.processingTimes
end Lax434175.PreemptiveShopProblems.FieldName.processingTimes

namespace Lax434175.PreemptiveShopProblems.FieldName.releaseDates
end Lax434175.PreemptiveShopProblems.FieldName.releaseDates

namespace Lax434175.PreemptiveShopProblems.FieldName.shopType
end Lax434175.PreemptiveShopProblems.FieldName.shopType
end

-- Lax434175.Servers
section
namespace Lax434175.Servers
end Lax434175.Servers

namespace Lax434175.Servers.Admits
end Lax434175.Servers.Admits

namespace Lax434175.Servers.Data
end Lax434175.Servers.Data

namespace Lax434175.Servers.Value
end Lax434175.Servers.Value

namespace Lax434175.Servers.embed
end Lax434175.Servers.embed

namespace Lax434175.Servers.le
end Lax434175.Servers.le

namespace Lax434175.Servers.view
end Lax434175.Servers.view

namespace Lax434175.Servers.Value.arbitrary
end Lax434175.Servers.Value.arbitrary

namespace Lax434175.Servers.Value.equal
end Lax434175.Servers.Value.equal

namespace Lax434175.Servers.Value.none
end Lax434175.Servers.Value.none

namespace Lax434175.Servers.Value.unit
end Lax434175.Servers.Value.unit
end

-- Lax434175.ShopExtras
section
namespace Lax434175.ShopExtras
end Lax434175.ShopExtras

namespace Lax434175.ShopExtras.BatchSetups
end Lax434175.ShopExtras.BatchSetups

namespace Lax434175.ShopExtras.NoIdle
end Lax434175.ShopExtras.NoIdle

namespace Lax434175.ShopExtras.BatchSetups.Data
end Lax434175.ShopExtras.BatchSetups.Data

namespace Lax434175.ShopExtras.BatchSetups.batch
end Lax434175.ShopExtras.BatchSetups.batch

namespace Lax434175.ShopExtras.BatchSetups.batchSetups
end Lax434175.ShopExtras.BatchSetups.batchSetups

namespace Lax434175.ShopExtras.BatchSetups.embed
end Lax434175.ShopExtras.BatchSetups.embed

namespace Lax434175.ShopExtras.BatchSetups.le
end Lax434175.ShopExtras.BatchSetups.le

namespace Lax434175.ShopExtras.BatchSetups.none
end Lax434175.ShopExtras.BatchSetups.none

namespace Lax434175.ShopExtras.NoIdle.noIdle
end Lax434175.ShopExtras.NoIdle.noIdle

namespace Lax434175.ShopExtras.NoIdle.none
end Lax434175.ShopExtras.NoIdle.none
end

-- Lax434175.Transportation
section
namespace Lax434175.Transportation
end Lax434175.Transportation

namespace Lax434175.Transportation.Shape
end Lax434175.Transportation.Shape

namespace Lax434175.Transportation.Value
end Lax434175.Transportation.Value

namespace Lax434175.Transportation.Shape.holds
end Lax434175.Transportation.Shape.holds

namespace Lax434175.Transportation.Shape.job
end Lax434175.Transportation.Shape.job

namespace Lax434175.Transportation.Shape.jobPair
end Lax434175.Transportation.Shape.jobPair

namespace Lax434175.Transportation.Shape.jobPairSymmetric
end Lax434175.Transportation.Shape.jobPairSymmetric

namespace Lax434175.Transportation.Shape.jobSource
end Lax434175.Transportation.Shape.jobSource

namespace Lax434175.Transportation.Shape.le
end Lax434175.Transportation.Shape.le

namespace Lax434175.Transportation.Shape.none
end Lax434175.Transportation.Shape.none

namespace Lax434175.Transportation.Shape.pair
end Lax434175.Transportation.Shape.pair

namespace Lax434175.Transportation.Shape.pairSymmetric
end Lax434175.Transportation.Shape.pairSymmetric

namespace Lax434175.Transportation.Shape.source
end Lax434175.Transportation.Shape.source

namespace Lax434175.Transportation.Shape.twoValues
end Lax434175.Transportation.Shape.twoValues

namespace Lax434175.Transportation.Shape.uniform
end Lax434175.Transportation.Shape.uniform
end

-- Lax434175.ShopProblems
section
namespace Lax434175.ShopProblems
end Lax434175.ShopProblems

namespace Lax434175.ShopProblems.FieldName
end Lax434175.ShopProblems.FieldName

namespace Lax434175.ShopProblems.family
end Lax434175.ShopProblems.family

namespace Lax434175.ShopProblems.spec
end Lax434175.ShopProblems.spec

namespace Lax434175.ShopProblems.FieldName.batchSetups
end Lax434175.ShopProblems.FieldName.batchSetups

namespace Lax434175.ShopProblems.FieldName.deadlines
end Lax434175.ShopProblems.FieldName.deadlines

namespace Lax434175.ShopProblems.FieldName.jobCount
end Lax434175.ShopProblems.FieldName.jobCount

namespace Lax434175.ShopProblems.FieldName.machineCount
end Lax434175.ShopProblems.FieldName.machineCount

namespace Lax434175.ShopProblems.FieldName.machineSets
end Lax434175.ShopProblems.FieldName.machineSets

namespace Lax434175.ShopProblems.FieldName.noIdle
end Lax434175.ShopProblems.FieldName.noIdle

namespace Lax434175.ShopProblems.FieldName.noWait
end Lax434175.ShopProblems.FieldName.noWait

namespace Lax434175.ShopProblems.FieldName.precedence
end Lax434175.ShopProblems.FieldName.precedence

namespace Lax434175.ShopProblems.FieldName.processingTimes
end Lax434175.ShopProblems.FieldName.processingTimes

namespace Lax434175.ShopProblems.FieldName.releaseDates
end Lax434175.ShopProblems.FieldName.releaseDates

namespace Lax434175.ShopProblems.FieldName.server
end Lax434175.ShopProblems.FieldName.server

namespace Lax434175.ShopProblems.FieldName.shopType
end Lax434175.ShopProblems.FieldName.shopType

namespace Lax434175.ShopProblems.FieldName.transportation
end Lax434175.ShopProblems.FieldName.transportation
end

-- Lax434175.ShopFamily
section
namespace Lax434175.ShopFamily
end Lax434175.ShopFamily

namespace Lax434175.ShopFamily.FieldName
end Lax434175.ShopFamily.FieldName

namespace Lax434175.ShopFamily.family
end Lax434175.ShopFamily.family

namespace Lax434175.ShopFamily.holds
end Lax434175.ShopFamily.holds

namespace Lax434175.ShopFamily.spec
end Lax434175.ShopFamily.spec

namespace Lax434175.ShopFamily.FieldName.field
end Lax434175.ShopFamily.FieldName.field

namespace Lax434175.ShopFamily.FieldName.interruption
end Lax434175.ShopFamily.FieldName.interruption
end

-- Lax434175.Operations
section
namespace Lax434175.Operations.Structure
end Lax434175.Operations.Structure

namespace Lax434175.Operations.environmentHolds
end Lax434175.Operations.environmentHolds

namespace Lax434175.Operations.holds
end Lax434175.Operations.holds

namespace Lax434175.Operations.processingTimesHolds
end Lax434175.Operations.processingTimesHolds

namespace Lax434175.Operations.Structure.flexibleFlow
end Lax434175.Operations.Structure.flexibleFlow

namespace Lax434175.Operations.Structure.flow
end Lax434175.Operations.Structure.flow

namespace Lax434175.Operations.Structure.holds
end Lax434175.Operations.Structure.holds

namespace Lax434175.Operations.Structure.job
end Lax434175.Operations.Structure.job

namespace Lax434175.Operations.Structure.le
end Lax434175.Operations.Structure.le

namespace Lax434175.Operations.Structure.open
end Lax434175.Operations.Structure.open

namespace Lax434175.Operations.Structure.ordered
end Lax434175.Operations.Structure.ordered

namespace Lax434175.Operations.Structure.single
end Lax434175.Operations.Structure.single

namespace Lax434175.Operations

open Lax434175.Kernels Lax434175.Modules Lax434175

structure Inst where
  jobs : ℕ
  machines : ℕ
  /-- The number of operations of a job. -/
  ops : Fin jobs → ℕ
  /-- The time an operation needs on a machine. -/
  p : (j : Fin jobs) → Fin (ops j) → Fin machines → ℕ
  /-- The release date of a job. -/
  r : Fin jobs → ℕ

/-- An operation: a job and a position in its sequence. -/
abbrev Op (x : Inst) := (j : Fin x.jobs) × Fin (x.ops j)

/-- The shop instance with the jobs, machines and operations of an instance. -/
abbrev Inst.toShop (x : Inst) : Shops.Inst := ⟨x.jobs, x.machines, x.ops, fun _ _ => 0, x.r⟩

/-- The parallel-machine instance with the jobs and machines of an instance. -/
abbrev Inst.toPar (x : Inst) : ParallelMachines.Inst := ⟨x.jobs, x.machines, fun _ _ => 0, x.r⟩

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

/-- The pieces of a job. -/
def piecesOfJob {x : Inst} (σ : Sched x) (j : Fin x.jobs) : List (Piece x) :=
  σ.pieces.filter (fun q => decide (q.op.1 = j))

/-- Two pieces do not overlap in time. -/
def Apart {x : Inst} (a b : Piece x) : Prop :=
  a.finish ≤ b.start ∨ b.finish ≤ a.start

/-- Every piece occupies some machine, and two different pieces that belong to
the same job or share a machine do not overlap. -/
def feasible {x : Inst} (σ : Sched x) : Prop :=
  (∀ q ∈ σ.pieces, q.machines.Nonempty) ∧
  σ.pieces.Pairwise (fun a b => (a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) → Apart a b)

/-- The kernel of scheduling with operations. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible _ σ := feasible σ
  start _ σ j := (((piecesOfJob σ j).map Piece.start).min?).getD 0
  completion _ σ j := (((piecesOfJob σ j).map Piece.finish).max?).getD 0

/-- A value of the machine field: a machine-set value of parallel machines,
which restricts every operation of a job alike, or a machine value of shops. -/
inductive Machines
  | par (v : MachineSets.Value)
  | shop (v : Shops.Machines)

/-- The data of a value. -/
def Machines.Data : Machines → Inst → Type
  | .par v, x => MachineSets.Data v x.toPar
  | .shop v, x => Shops.Machines.Data v x.toShop

/-- Whether an operation may occupy a set of machines. -/
def Machines.view {x : Inst} : (v : Machines) → v.Data x → Op x → Finset (Fin x.machines) → Prop
  | .par v, d => fun o S => MachineSets.view (x := x.toPar) v d o.1 S
  | .shop v, d => fun o S => Shops.Machines.view (x := x.toShop) v d o.1 o.2 S

/-- The condition on the data. -/
def Machines.admits {x : Inst} : (v : Machines) → v.Data x → Prop
  | .par _, _ => True
  | .shop v, d => Shops.Machines.admits (x := x.toShop) v d

/-- Which machine-set values of parallel machines are special cases of which
machine values of shops. -/
def crossLe : MachineSets.Value → Shops.Machines → Bool
  | .none, .sets | .sets, .sets | .fix, .fix => true
  | _, .general => true
  | _, _ => false

def Machines.le : Machines → Machines → Bool
  | .par v, .par w => MachineSets.le v w
  | .shop v, .shop w => Shops.Machines.le v w
  | .par v, .shop w => crossLe v w
  | .shop _, .par _ => false

/-- Machine-set data of parallel machines read as machine data of shops. -/
def crossEmbed : (v : MachineSets.Value) → (w : Shops.Machines) → crossLe v w = true →
    (x : Inst) → MachineSets.Data v x.toPar → Shops.Machines.Data w x.toShop
  | .none, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .none, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .none, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .none, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .none, .sets, _, _, _ => fun _ _ _ => True
  | .none, .fix, h, _, _ => absurd h Bool.false_ne_true
  | .none, .general, _, _, M => fun j _ S => MachineSets.view .none M j S
  | .sets, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .sets, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .sets, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .sets, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .sets, .sets, _, _, M => fun j _ i => M j i
  | .sets, .fix, h, _, _ => absurd h Bool.false_ne_true
  | .sets, .general, _, _, M => fun j _ S => MachineSets.view .sets M j S
  | .fix, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .fix, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .fix, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .fix, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .fix, .sets, h, _, _ => absurd h Bool.false_ne_true
  | .fix, .fix, _, _, M => fun j _ => M j
  | .fix, .general, _, _, M => fun j _ S => MachineSets.view .fix M j S
  | .sizeOneOrAll, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .sets, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .fix, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .general, _, _, M => fun j _ S => MachineSets.view .sizeOneOrAll M j S
  | .size, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .size, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .size, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .size, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .size, .sets, h, _, _ => absurd h Bool.false_ne_true
  | .size, .fix, h, _, _ => absurd h Bool.false_ne_true
  | .size, .general, _, _, M => fun j _ S => MachineSets.view .size M j S
  | .general, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .general, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .general, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .general, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .general, .sets, h, _, _ => absurd h Bool.false_ne_true
  | .general, .fix, h, _, _ => absurd h Bool.false_ne_true
  | .general, .general, _, _, M => fun j _ S => MachineSets.view .general M j S

def Machines.embed : {v w : Machines} → Machines.le v w = true → (x : Inst) →
    v.Data x → w.Data x
  | .par _, .par _, h, x, d => MachineSets.embed h x.toPar d
  | .shop _, .shop _, h, x, d => Shops.Machines.embed h x.toShop d
  | .par v, .shop w, h, x, d => crossEmbed v w h x d
  | .shop _, .par _, h, _, _ => absurd h Bool.false_ne_true

/-- The machine field. -/
def machineSets : Module kernel where
  Value := Machines
  Data := Machines.Data
  admits v _ d := v.admits d
  constraint v _ d σ := ∀ q ∈ σ.pieces, v.view d q.op q.machines
  le := Machines.le
  embed := Machines.embed

axiom machineSets_sound : machineSets.Sound

end Lax434175.Operations
end
