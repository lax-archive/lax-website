-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.Partrec
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype

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

/-- A field whose values add data to an instance and determine the cost of a
schedule. -/
structure Objective (K : Kernel) where
  Value : Type
  /-- The data a value adds to an instance. -/
  Data : Value → K.Inst → Type
  /-- The condition a value imposes on an instance and its data. -/
  admits : (v : Value) → (x : K.Inst) → Data v x → Prop
  /-- The cost of a schedule. -/
  cost : (v : Value) → (x : K.Inst) → Data v x → K.Sched x → ℚ
  /-- `le v w`: the value `v` is a special case of `w`. -/
  le : Value → Value → Bool
  /-- Data of a value read as data of a more general value. -/
  embed : {v w : Value} → le v w = true → (x : K.Inst) → Data v x → Data w x

/-- Reading data with a more general value keeps it admissible and does not
change the cost. -/
structure Objective.Sound {K : Kernel} (O : Objective K) : Prop where
  admits : ∀ (v w : O.Value) (h : O.le v w = true) (x : K.Inst) (d : O.Data v x),
    O.admits v x d → O.admits w x (O.embed h x d)
  cost : ∀ (v w : O.Value) (h : O.le v w = true) (x : K.Inst) (d : O.Data v x)
    (σ : K.Sched x), O.cost w x (O.embed h x d) σ = O.cost v x d σ

end Lax434175.Modules
end

-- Lax434175.Problems
section
namespace Lax434175.Problems.DecisionReduction
end Lax434175.Problems.DecisionReduction

namespace Lax434175.Problems.Embedding.Sound
end Lax434175.Problems.Embedding.Sound

namespace Lax434175.Problems

/-- A minimization problem. -/
structure Problem where
  /-- The instances. -/
  Inst : Type
  /-- The candidate solutions of an instance. -/
  Sched : Inst → Type
  /-- Which candidate solutions are feasible. -/
  feasible : (x : Inst) → Sched x → Prop
  /-- The cost of a candidate solution. -/
  cost : (x : Inst) → Sched x → ℚ

/-- The data of an embedding of `A` into `B`: a map on instances and
translations of solutions in both directions. -/
structure Embedding (A B : Problem) where
  map : A.Inst → B.Inst
  forth : (x : A.Inst) → A.Sched x → B.Sched (map x)
  back : (x : A.Inst) → B.Sched (map x) → A.Sched x

/-- Some feasible solution of the instance has cost at most the threshold. -/
def Problem.Decides (P : Problem) (x : P.Inst) (D : ℚ) : Prop :=
  ∃ σ, P.feasible x σ ∧ P.cost x σ ≤ D

end Lax434175.Problems
end

-- Lax434175.Assembly
section
namespace Lax434175.Assembly

open Lax434175.Problems Lax434175.Kernels Lax434175.Modules

/-- The fields from which problems over a kernel are assembled. -/
structure Family (K : Kernel) where
  /-- The names of the constraint fields. -/
  ModuleName : Type
  module : ModuleName → Module K
  objective : Objective K

/-- A choice of one value in every field. -/
structure Spec {K : Kernel} (F : Family K) where
  module : (i : F.ModuleName) → (F.module i).Value
  objective : F.objective.Value

/-- An instance of the problem described by a specification. -/
structure Inst {K : Kernel} (F : Family K) (s : Spec F) where
  base : K.Inst
  data : (i : F.ModuleName) → (F.module i).Data (s.module i) base
  admitted : ∀ i, (F.module i).admits (s.module i) base (data i)
  objectiveData : F.objective.Data s.objective base
  objectiveAdmitted : F.objective.admits s.objective base objectiveData

/-- The problem described by a specification. -/
def problem {K : Kernel} (F : Family K) (s : Spec F) : Problem where
  Inst := Inst F s
  Sched x := K.Sched x.base
  feasible x σ :=
    K.feasible x.base σ ∧ ∀ i, (F.module i).constraint (s.module i) x.base (x.data i) σ
  cost x σ := F.objective.cost s.objective x.base x.objectiveData σ

/-- Field-wise comparison of specifications. -/
def Spec.le {K : Kernel} {F : Family K} (s t : Spec F) : Prop :=
  (∀ i, (F.module i).le (s.module i) (t.module i) = true) ∧
    F.objective.le s.objective t.objective = true

/-- All fields of a family are sound. -/
structure Family.Sound {K : Kernel} (F : Family K) : Prop where
  module : ∀ i, (F.module i).Sound
  objective : F.objective.Sound

/-- The embedding induced by a field-wise comparison. The kernel instance and
the schedule are unchanged; the data of each field is read with the more
general value. -/
def lift {K : Kernel} (F : Family K) (hF : F.Sound) {s t : Spec F} (h : s.le t) :
    Embedding (problem F s) (problem F t) where
  map x :=
    { base := x.base
      data := fun i => (F.module i).embed (h.1 i) x.base (x.data i)
      admitted := fun i => (hF.module i).admits _ _ (h.1 i) x.base (x.data i) (x.admitted i)
      objectiveData := F.objective.embed h.2 x.base x.objectiveData
      objectiveAdmitted :=
        hF.objective.admits _ _ h.2 x.base x.objectiveData x.objectiveAdmitted }
  forth _ σ := σ
  back _ σ := σ

end Lax434175.Assembly
end

-- Lax434175.Batching
section
namespace Lax434175.Batching
end Lax434175.Batching

namespace Lax434175.Batching.Capacity
end Lax434175.Batching.Capacity

namespace Lax434175.Batching.Inst
end Lax434175.Batching.Inst

namespace Lax434175.Batching.Mode
end Lax434175.Batching.Mode

namespace Lax434175.Batching.ProcessingTimes
end Lax434175.Batching.ProcessingTimes

namespace Lax434175.Batching.Sched
end Lax434175.Batching.Sched

namespace Lax434175.Batching.length
end Lax434175.Batching.length

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

namespace Lax434175.Batching.Mode.parallel
end Lax434175.Batching.Mode.parallel

namespace Lax434175.Batching.Mode.serial
end Lax434175.Batching.Mode.serial

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

-- Lax434175.BatchProblems
section
namespace Lax434175.BatchProblems
end Lax434175.BatchProblems

namespace Lax434175.BatchProblems.FieldName
end Lax434175.BatchProblems.FieldName

namespace Lax434175.BatchProblems.family
end Lax434175.BatchProblems.family

namespace Lax434175.BatchProblems.spec
end Lax434175.BatchProblems.spec

namespace Lax434175.BatchProblems.FieldName.capacity
end Lax434175.BatchProblems.FieldName.capacity

namespace Lax434175.BatchProblems.FieldName.deadlines
end Lax434175.BatchProblems.FieldName.deadlines

namespace Lax434175.BatchProblems.FieldName.jobCount
end Lax434175.BatchProblems.FieldName.jobCount

namespace Lax434175.BatchProblems.FieldName.precedence
end Lax434175.BatchProblems.FieldName.precedence

namespace Lax434175.BatchProblems.FieldName.processingTimes
end Lax434175.BatchProblems.FieldName.processingTimes

namespace Lax434175.BatchProblems.FieldName.releaseDates
end Lax434175.BatchProblems.FieldName.releaseDates
end

-- Lax434175.BatchFamily
section
namespace Lax434175.BatchFamily
end Lax434175.BatchFamily

namespace Lax434175.BatchFamily.FieldName
end Lax434175.BatchFamily.FieldName

namespace Lax434175.BatchFamily.Sched
end Lax434175.BatchFamily.Sched

namespace Lax434175.BatchFamily.family
end Lax434175.BatchFamily.family

namespace Lax434175.BatchFamily.modeLe
end Lax434175.BatchFamily.modeLe

namespace Lax434175.BatchFamily.spec
end Lax434175.BatchFamily.spec

namespace Lax434175.BatchFamily.FieldName.field
end Lax434175.BatchFamily.FieldName.field

namespace Lax434175.BatchFamily.FieldName.mode
end Lax434175.BatchFamily.FieldName.mode
end

-- Lax434175.MachineCovering
section
namespace Lax434175.MachineCovering
end Lax434175.MachineCovering

namespace Lax434175.MachineCovering.Inst
end Lax434175.MachineCovering.Inst
end

-- Lax434175.ParallelMachines
section
namespace Lax434175.ParallelMachines
end Lax434175.ParallelMachines

namespace Lax434175.ParallelMachines.Environment
end Lax434175.ParallelMachines.Environment

namespace Lax434175.ParallelMachines.Inst
end Lax434175.ParallelMachines.Inst

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
end Lax434175.MachineSets

namespace Lax434175.MachineSets.Data
end Lax434175.MachineSets.Data

namespace Lax434175.MachineSets.Value
end Lax434175.MachineSets.Value

namespace Lax434175.MachineSets.embed
end Lax434175.MachineSets.embed

namespace Lax434175.MachineSets.le
end Lax434175.MachineSets.le

namespace Lax434175.MachineSets.view
end Lax434175.MachineSets.view

namespace Lax434175.MachineSets.Value.fix
end Lax434175.MachineSets.Value.fix

namespace Lax434175.MachineSets.Value.general
end Lax434175.MachineSets.Value.general

namespace Lax434175.MachineSets.Value.none
end Lax434175.MachineSets.Value.none

namespace Lax434175.MachineSets.Value.sets
end Lax434175.MachineSets.Value.sets

namespace Lax434175.MachineSets.Value.size
end Lax434175.MachineSets.Value.size

namespace Lax434175.MachineSets.Value.sizeOneOrAll
end Lax434175.MachineSets.Value.sizeOneOrAll
end

-- Lax434175.Shops
section
namespace Lax434175.Shops
end Lax434175.Shops

namespace Lax434175.Shops.Inst
end Lax434175.Shops.Inst

namespace Lax434175.Shops.Machines
end Lax434175.Shops.Machines

namespace Lax434175.Shops.NoWait
end Lax434175.Shops.NoWait

namespace Lax434175.Shops.ProcessingTimes
end Lax434175.Shops.ProcessingTimes

namespace Lax434175.Shops.Sched
end Lax434175.Shops.Sched

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
namespace Lax434175.Operations
end Lax434175.Operations

namespace Lax434175.Operations.Inst
end Lax434175.Operations.Inst

namespace Lax434175.Operations.Machines
end Lax434175.Operations.Machines

namespace Lax434175.Operations.Piece
end Lax434175.Operations.Piece

namespace Lax434175.Operations.Sched
end Lax434175.Operations.Sched

namespace Lax434175.Operations.Structure
end Lax434175.Operations.Structure

namespace Lax434175.Operations.crossEmbed
end Lax434175.Operations.crossEmbed

namespace Lax434175.Operations.crossLe
end Lax434175.Operations.crossLe

namespace Lax434175.Operations.environmentHolds
end Lax434175.Operations.environmentHolds

namespace Lax434175.Operations.holds
end Lax434175.Operations.holds

namespace Lax434175.Operations.processingTimesHolds
end Lax434175.Operations.processingTimesHolds

namespace Lax434175.Operations.Machines.Data
end Lax434175.Operations.Machines.Data

namespace Lax434175.Operations.Machines.embed
end Lax434175.Operations.Machines.embed

namespace Lax434175.Operations.Machines.le
end Lax434175.Operations.Machines.le

namespace Lax434175.Operations.Machines.par
end Lax434175.Operations.Machines.par

namespace Lax434175.Operations.Machines.shop
end Lax434175.Operations.Machines.shop

namespace Lax434175.Operations.Machines.view
end Lax434175.Operations.Machines.view

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
end

-- Lax434175.CommunicationDelays
section
namespace Lax434175.CommunicationDelays
end Lax434175.CommunicationDelays

namespace Lax434175.CommunicationDelays.Data
end Lax434175.CommunicationDelays.Data

namespace Lax434175.CommunicationDelays.Value
end Lax434175.CommunicationDelays.Value

namespace Lax434175.CommunicationDelays.embed
end Lax434175.CommunicationDelays.embed

namespace Lax434175.CommunicationDelays.le
end Lax434175.CommunicationDelays.le

namespace Lax434175.CommunicationDelays.view
end Lax434175.CommunicationDelays.view

namespace Lax434175.CommunicationDelays.Value.general
end Lax434175.CommunicationDelays.Value.general

namespace Lax434175.CommunicationDelays.Value.none
end Lax434175.CommunicationDelays.Value.none

namespace Lax434175.CommunicationDelays.Value.unit
end Lax434175.CommunicationDelays.Value.unit
end

-- Lax434175.ForbiddenTimes
section
namespace Lax434175.ForbiddenTimes
end Lax434175.ForbiddenTimes

namespace Lax434175.ForbiddenTimes.Data
end Lax434175.ForbiddenTimes.Data

namespace Lax434175.ForbiddenTimes.Encoding
end Lax434175.ForbiddenTimes.Encoding

namespace Lax434175.ForbiddenTimes.Value
end Lax434175.ForbiddenTimes.Value

namespace Lax434175.ForbiddenTimes.embed
end Lax434175.ForbiddenTimes.embed

namespace Lax434175.ForbiddenTimes.le
end Lax434175.ForbiddenTimes.le

namespace Lax434175.ForbiddenTimes.view
end Lax434175.ForbiddenTimes.view

namespace Lax434175.ForbiddenTimes.Encoding.highMultiplicity
end Lax434175.ForbiddenTimes.Encoding.highMultiplicity

namespace Lax434175.ForbiddenTimes.Encoding.standard
end Lax434175.ForbiddenTimes.Encoding.standard

namespace Lax434175.ForbiddenTimes.Value.forbidden
end Lax434175.ForbiddenTimes.Value.forbidden

namespace Lax434175.ForbiddenTimes.Value.none
end Lax434175.ForbiddenTimes.Value.none
end

-- Lax434175.Nonpreemptive
section
namespace Lax434175.Nonpreemptive
end Lax434175.Nonpreemptive

namespace Lax434175.Nonpreemptive.Sched
end Lax434175.Nonpreemptive.Sched
end

-- Lax434175.ParallelProblems
section
namespace Lax434175.ParallelProblems
end Lax434175.ParallelProblems

namespace Lax434175.ParallelProblems.FieldName
end Lax434175.ParallelProblems.FieldName

namespace Lax434175.ParallelProblems.family
end Lax434175.ParallelProblems.family

namespace Lax434175.ParallelProblems.spec
end Lax434175.ParallelProblems.spec

namespace Lax434175.ParallelProblems.FieldName.communicationDelays
end Lax434175.ParallelProblems.FieldName.communicationDelays

namespace Lax434175.ParallelProblems.FieldName.deadlines
end Lax434175.ParallelProblems.FieldName.deadlines

namespace Lax434175.ParallelProblems.FieldName.encoding
end Lax434175.ParallelProblems.FieldName.encoding

namespace Lax434175.ParallelProblems.FieldName.environment
end Lax434175.ParallelProblems.FieldName.environment

namespace Lax434175.ParallelProblems.FieldName.forbiddenTimes
end Lax434175.ParallelProblems.FieldName.forbiddenTimes

namespace Lax434175.ParallelProblems.FieldName.jobCount
end Lax434175.ParallelProblems.FieldName.jobCount

namespace Lax434175.ParallelProblems.FieldName.machineCount
end Lax434175.ParallelProblems.FieldName.machineCount

namespace Lax434175.ParallelProblems.FieldName.machineSets
end Lax434175.ParallelProblems.FieldName.machineSets

namespace Lax434175.ParallelProblems.FieldName.precedence
end Lax434175.ParallelProblems.FieldName.precedence

namespace Lax434175.ParallelProblems.FieldName.processingTimes
end Lax434175.ParallelProblems.FieldName.processingTimes

namespace Lax434175.ParallelProblems.FieldName.releaseDates
end Lax434175.ParallelProblems.FieldName.releaseDates

namespace Lax434175.ParallelProblems.FieldName.server
end Lax434175.ParallelProblems.FieldName.server
end

-- Lax434175.ParallelFamily
section
namespace Lax434175.ParallelFamily
end Lax434175.ParallelFamily

namespace Lax434175.ParallelFamily.FieldName
end Lax434175.ParallelFamily.FieldName

namespace Lax434175.ParallelFamily.family
end Lax434175.ParallelFamily.family

namespace Lax434175.ParallelFamily.ofSpec
end Lax434175.ParallelFamily.ofSpec

namespace Lax434175.ParallelFamily.spec
end Lax434175.ParallelFamily.spec

namespace Lax434175.ParallelFamily.transSpec
end Lax434175.ParallelFamily.transSpec

namespace Lax434175.ParallelFamily.FieldName.field
end Lax434175.ParallelFamily.FieldName.field

namespace Lax434175.ParallelFamily.FieldName.interruption
end Lax434175.ParallelFamily.FieldName.interruption
end

-- Lax434175.OperationsFamily
section
namespace Lax434175.OperationsFamily
end Lax434175.OperationsFamily

namespace Lax434175.OperationsFamily.FieldName
end Lax434175.OperationsFamily.FieldName

namespace Lax434175.OperationsFamily.family
end Lax434175.OperationsFamily.family

namespace Lax434175.OperationsFamily.ofShopTimes
end Lax434175.OperationsFamily.ofShopTimes

namespace Lax434175.OperationsFamily.ofShopType
end Lax434175.OperationsFamily.ofShopType

namespace Lax434175.OperationsFamily.spec
end Lax434175.OperationsFamily.spec

namespace Lax434175.OperationsFamily.FieldName.batchSetups
end Lax434175.OperationsFamily.FieldName.batchSetups

namespace Lax434175.OperationsFamily.FieldName.communicationDelays
end Lax434175.OperationsFamily.FieldName.communicationDelays

namespace Lax434175.OperationsFamily.FieldName.deadlines
end Lax434175.OperationsFamily.FieldName.deadlines

namespace Lax434175.OperationsFamily.FieldName.encoding
end Lax434175.OperationsFamily.FieldName.encoding

namespace Lax434175.OperationsFamily.FieldName.environment
end Lax434175.OperationsFamily.FieldName.environment

namespace Lax434175.OperationsFamily.FieldName.forbiddenTimes
end Lax434175.OperationsFamily.FieldName.forbiddenTimes

namespace Lax434175.OperationsFamily.FieldName.interruption
end Lax434175.OperationsFamily.FieldName.interruption

namespace Lax434175.OperationsFamily.FieldName.jobCount
end Lax434175.OperationsFamily.FieldName.jobCount

namespace Lax434175.OperationsFamily.FieldName.jobStructure
end Lax434175.OperationsFamily.FieldName.jobStructure

namespace Lax434175.OperationsFamily.FieldName.machineCount
end Lax434175.OperationsFamily.FieldName.machineCount

namespace Lax434175.OperationsFamily.FieldName.machineSets
end Lax434175.OperationsFamily.FieldName.machineSets

namespace Lax434175.OperationsFamily.FieldName.noIdle
end Lax434175.OperationsFamily.FieldName.noIdle

namespace Lax434175.OperationsFamily.FieldName.noWait
end Lax434175.OperationsFamily.FieldName.noWait

namespace Lax434175.OperationsFamily.FieldName.precedence
end Lax434175.OperationsFamily.FieldName.precedence

namespace Lax434175.OperationsFamily.FieldName.processingTimes
end Lax434175.OperationsFamily.FieldName.processingTimes

namespace Lax434175.OperationsFamily.FieldName.releaseDates
end Lax434175.OperationsFamily.FieldName.releaseDates

namespace Lax434175.OperationsFamily.FieldName.server
end Lax434175.OperationsFamily.FieldName.server

namespace Lax434175.OperationsFamily.FieldName.transportation
end Lax434175.OperationsFamily.FieldName.transportation
end

-- Lax434175.Rejection
section
namespace Lax434175.Rejection
end Lax434175.Rejection

namespace Lax434175.Rejection.Inst
end Lax434175.Rejection.Inst

namespace Lax434175.Rejection.Sched
end Lax434175.Rejection.Sched
end

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax429075.CNF
section
namespace Lax429075
end Lax429075

namespace Lax429075.CNF
end Lax429075.CNF

namespace Lax429075.CNF.Literal
end Lax429075.CNF.Literal
end

-- Lax434175.Online
section
namespace Lax434175.Online.Causal
end Lax434175.Online.Causal

namespace Lax434175.Online.Hard
end Lax434175.Online.Hard

namespace Lax434175.Online.Randomized
end Lax434175.Online.Randomized

namespace Lax434175.Online

open Lax434175.Problems

/-- How the instances of a problem are revealed over time. -/
structure Revelation (P : Problem) where
  /-- The two instances look the same to the scheduler at time `t`. -/
  same : P.Inst → P.Inst → NNRat → Prop
  /-- Two schedules of two instances made the same decisions up to time `t`. -/
  agree : (x y : P.Inst) → P.Sched x → P.Sched y → NNRat → Prop

variable {P : Problem}

end Lax434175.Online
end

-- Lax759944.BinaryWordEncoding
section
set_option backward.isDefEq.respectTransparency false

namespace Lax759944.BinaryWordEncoding

/-- The finite alphabet used to encode lists of natural numbers. -/
inductive Symbol
  | separator
  | zero
  | one
  deriving DecidableEq, Fintype, Inhabited

/-- Encode one natural number, including the separator which begins it. -/
def encodeNat (n : ℕ) : List Symbol :=
  .separator :: n.bits.map (fun b => if b then .one else .zero)

/-- The canonical binary encoding of a finite list of natural numbers. -/
def encode (x : List ℕ) : List Symbol :=
  x.flatMap encodeNat

/-- The bit-size of a finite list of natural numbers. -/
def bitSize (x : List ℕ) : ℕ :=
  (encode x).length

end Lax759944.BinaryWordEncoding
end

-- Lax808846.Ram
section
namespace Lax808846.Ram

/-- An instruction. Every number naming a cell is read, except that
the first one names the destination for instructions that write a cell,
and the cell holding the destination address for `store`. `set` carries
a literal value; `jump`, `jzero`, and `jeof` carry program labels,
which are not data-memory addresses. -/
inductive Instr
  /-- Set cell `a` to the literal `n`. -/
  | set (a n : ℕ)
  /-- Set cell `a` to the contents of the cell whose address cell `b`
  holds. -/
  | load (a b : ℕ)
  /-- Set the cell whose address cell `a` holds to the contents of cell
  `b`. -/
  | store (a b : ℕ)
  /-- Set cell `a` to the sum of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | add (a b c : ℕ)
  /-- Set cell `a` to the difference of cells `b` and `c`, truncated at
  zero rather than wrapping around. -/
  | sub (a b c : ℕ)
  /-- Set cell `a` to the product of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | mul (a b c : ℕ)
  /-- Set cell `a` to the quotient of cells `b` and `c`, rounding
  towards zero; division by zero yields zero. -/
  | div (a b c : ℕ)
  /-- Set cell `a` to the bitwise conjunction of cells `b` and `c`. -/
  | and (a b c : ℕ)
  /-- Set cell `a` to cell `b` shifted left by the number of bits cell
  `c` holds, wrapping around modulo `2 ^ w`; a shift by `w` or more
  yields zero. -/
  | shiftl (a b c : ℕ)
  /-- Set cell `a` to the bitwise complement `2 ^ w - 1 - m[b]` of cell
  `b` within the word length. -/
  | not (a b : ℕ)
  /-- Continue at instruction `l`. -/
  | jump (l : ℕ)
  /-- Continue at instruction `l` if cell `a` is zero. -/
  | jzero (a l : ℕ)
  /-- Continue at instruction `l` exactly when the remaining input tape
  is empty. This test does not consume input. -/
  | jeof (l : ℕ)
  /-- Write the original input length, reduced to a word, into cell `a`. -/
  | inputLength (a : ℕ)
  /-- Read original input at the word index in cell `b` into cell `a`,
  returning zero outside the input. Read the index before writing `a`,
  even when the two cell addresses coincide. Do not consume input. -/
  | inputLoad (a b : ℕ)
  /-- Halt. -/
  | halt
  /-- Read the next number of the input tape into cell `a`, or halt if
  the tape is exhausted. -/
  | read (a : ℕ)
  /-- Append the contents of cell `a` to the output tape. -/
  | write (a : ℕ)

/-- A program: a finite sequence of instructions, numbered from `0`. -/
abbrev Program : Type := List Instr

/-- A machine state: the program counter, the contents of every memory
cell, the immutable original input array, the remaining sequential input
tape, and the output tape written so far. -/
structure State where
  /-- The number of the instruction to be executed next. -/
  pc : ℕ
  /-- The contents of the memory cells; only the cells with number below
  `2 ^ w` are ever addressed. -/
  mem : ℕ → ℕ
  /-- The original read-only input, unchanged by every instruction. -/
  input : List ℕ
  /-- The numbers still to be read from the input tape. -/
  inp : List ℕ
  /-- The numbers written to the output tape so far. -/
  out : List ℕ

/-- The memory `m` with cell `a` set to `v`, at word length `w`: the
address and the value written are both taken modulo `2 ^ w`. -/
def setCell (w : ℕ) (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ :=
  fun b => if b = a % 2 ^ w then v % 2 ^ w else m b

/-- The effect of one instruction on the state at word length `w`, or
`none` if it halts the machine, which a `halt` instruction and a read
from an exhausted input tape do. Data values, input indices, and
data-memory addresses are reduced modulo `2 ^ w`; program labels and
the counter are not. -/
def Instr.effect (w : ℕ) : Instr → State → Option State
  | set a n, s => some { s with pc := s.pc + 1, mem := setCell w s.mem a n }
  | load a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (s.mem (b % 2 ^ w) % 2 ^ w)) }
  | store a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem (s.mem (a % 2 ^ w)) (s.mem (b % 2 ^ w)) }
  | add a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) + s.mem (c % 2 ^ w)) }
  | sub a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) - s.mem (c % 2 ^ w)) }
  | mul a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * s.mem (c % 2 ^ w)) }
  | div a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) / s.mem (c % 2 ^ w)) }
  | and a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (Nat.land (s.mem (b % 2 ^ w)) (s.mem (c % 2 ^ w))) }
  | shiftl a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * 2 ^ s.mem (c % 2 ^ w)) }
  | not a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (2 ^ w - 1 - s.mem (b % 2 ^ w)) }
  | jump l, s => some { s with pc := l }
  | jzero a l, s => some { s with pc := if s.mem (a % 2 ^ w) = 0 then l else s.pc + 1 }
  | jeof l, s => some { s with pc := if s.inp.isEmpty then l else s.pc + 1 }
  | inputLength a, s =>
      some { s with pc := s.pc + 1, mem := setCell w s.mem a s.input.length }
  | inputLoad a b, s =>
      some { s with
        pc := s.pc + 1
        mem := setCell w s.mem a (s.input[s.mem (b % 2 ^ w) % 2 ^ w]?.getD 0) }
  | halt, _ => none
  | read a, s =>
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := setCell w s.mem a v, inp := s.inp.tail }
  | write a, s =>
      some { s with pc := s.pc + 1, out := s.out ++ [s.mem (a % 2 ^ w) % 2 ^ w] }

/-- One step of the machine at word length `w`: fetch the instruction
the program counter points at and execute it. The result is `none` if
the machine has halted, which also happens when the program counter has
run past the program. -/
def step (w : ℕ) (p : Program) (s : State) : Option State :=
  p[s.pc]?.bind fun i => i.effect w s

/-- The state after `t` successful transitions at word length `w`, or
`none` if one of those transitions terminates. This auxiliary count does
not include a fetched terminal instruction; `RunsTo` charges that too. -/
def run (w : ℕ) (p : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step w p s).bind (run w p t)

/-- The initial state on input `x`: program counter zero, all memory
cells zero, the original input array and its sequential tape both `x`,
and the output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  mem := fun _ => 0
  input := x
  inp := x
  out := []

/-- Cost of termination at `s`, when `step w p s = none`: a fetched
terminal instruction costs one, while an out-of-range program counter
costs zero because there is no instruction to execute. -/
def terminalCost (p : Program) (s : State) : ℕ :=
  if s.pc < p.length then 1 else 0

/-- Started on input `x` at word length `w`, the machine executes
exactly `t` instructions and then halts, having written the word `y` to
its output tape. -/
def RunsTo (w : ℕ) (p : Program) (x y : List ℕ) (t : ℕ) : Prop :=
  ∃ (k : ℕ) (s : State), run w p k (initState x) = some s ∧
    step w p s = none ∧ s.out = y ∧ t = k + terminalCost p s

end Lax808846.Ram
end

-- Lax759944.RamPolytime
section
namespace Lax759944.RamPolytime

open Lax808846.Ram

open Lax759944.BinaryWordEncoding

/-- Every entry of `x` is representable by a word of `w` bits. -/
def FitsInWords (w : ℕ) (x : List ℕ) : Prop :=
  ∀ a ∈ x, a < 2 ^ w

end Lax759944.RamPolytime
end

-- Lax496464.WH_A1_FptTime
section
namespace Lax496464.WH_A1_FptTime

open Lax808846.Ram Lax759944.BinaryWordEncoding Lax759944.RamPolytime

/-- The fixed-parameter bound `f(k) · (n + 1)^d`, for a parameter value `k` and an input size `n`. -/
def fptBound (f : ℕ → ℕ) (d k n : ℕ) : ℕ := f k * (n + 1) ^ d

/-- On every word `x` of `D`, the program `p` computes `F x` from the tape `x.length :: x`
within `B = f(κ x) · (bitSize x + 1)^d` instructions, at every word length `w ≥ B`; and the
tape and the output fit in words of length `B`. -/
def ComputesInFptTime (p : Program) (D : Set (List ℕ)) (κ : List ℕ → ℕ)
    (F : List ℕ → List ℕ) (f : ℕ → ℕ) (d : ℕ) : Prop :=
  ∀ x ∈ D,
    FitsInWords (fptBound f d (κ x) (bitSize x)) ((x.length :: x) ++ F x) ∧
      ∀ w : ℕ, fptBound f d (κ x) (bitSize x) ≤ w →
        ∃ t ≤ fptBound f d (κ x) (bitSize x), RunsTo w p (x.length :: x) (F x) t

/-- **Fixed-parameter time.** `F` is computable on the words of `D` in time `f(κ x) · (|x| + 1)^d`
by one program, for a computable `f` and a constant `d`. -/
def FptTimeOn (D : Set (List ℕ)) (κ : List ℕ → ℕ) (F : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (f : ℕ → ℕ) (d : ℕ), Computable f ∧ ComputesInFptTime p D κ F f d

end Lax496464.WH_A1_FptTime
end

-- Lax808846.RamComputes
section
namespace Lax808846.RamComputes

open Lax808846.Ram

/-- At word length `w`, on every admissible input `x`, the program halts
within `T x` executed instructions with output `f x`. -/
def ComputesInTime (w : ℕ) (p : Program) (D : Set (List ℕ))
    (f : List ℕ → List ℕ) (T : List ℕ → ℕ) : Prop :=
  ∀ x ∈ D, ∃ t ≤ T x, RunsTo w p x (f x) t

end Lax808846.RamComputes
end

-- Lax888481.ParameterizedComplexity
section
namespace Lax888481.ParameterizedComplexity

open Lax808846.Ram Lax808846.RamComputes

/-- A parameterized problem: the words that encode an instance, which of them are
yes-instances, and the parameter each one carries. -/
structure Problem where
  /-- The words that encode an instance. A program may do anything on the others. -/
  Domain : Set (List ℕ)
  /-- The yes-instances. -/
  Yes : List ℕ → Prop
  /-- The parameter, read off the word. -/
  param : List ℕ → ℕ

/-- The word `x` fits at word length `w`, with room for `c` times its length: every
entry `v` of `x` satisfies `c * (x.length + v + 1) ≤ 2 ^ w`. -/
def Fits (c w : ℕ) (x : List ℕ) : Prop := ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w

/-- The map `f` is an fpt-reduction from `P` to `Q`, computed by `prog` within
`c * g k * (|x| + 1)` instructions and raising the parameter by at most `h`. -/
structure IsFptReduction (P Q : Problem) (f : List ℕ → List ℕ) (prog : Program)
    (c : ℕ) (g h : ℕ → ℕ) : Prop where
  /-- The image of an admissible word is admissible. -/
  maps_domain : ∀ x ∈ P.Domain, f x ∈ Q.Domain
  /-- Yes-instances go to yes-instances, and no-instances to no-instances. -/
  correct : ∀ x ∈ P.Domain, (P.Yes x ↔ Q.Yes (f x))
  /-- The new parameter is bounded by a function of the old one alone. -/
  param_le : ∀ x ∈ P.Domain, Q.param (f x) ≤ h (P.param x)
  /-- At every word length, the program computes `f` on every admissible word that fits
  and whose image fits, within the stated bound. -/
  time : ∀ w : ℕ, ComputesInTime w prog
    {x | x ∈ P.Domain ∧ Fits c w x ∧ Fits c w (f x)}
    f (fun x => c * g (P.param x) * (x.length + 1))

/-- `P` **fpt-reduces** to `Q`. -/
def FptReduces (P Q : Problem) : Prop :=
  ∃ (f : List ℕ → List ℕ) (prog : Program) (c : ℕ) (g h : ℕ → ℕ),
    IsFptReduction P Q f prog c g h

@[inherit_doc] infix:50 " ≤fpt " => FptReduces

end Lax888481.ParameterizedComplexity
end

-- Lax496464.WH_A2_FptReductions
section
namespace Lax496464.WH_A2_FptReductions

open Lax888481.ParameterizedComplexity (Problem)

open Lax496464.WH_A1_FptTime

/-- **Step 1 of a reduction: construction and correctness.** `R` maps instances of `P` to
instances of `Q`, yes-instances to yes-instances and no-instances to no-instances. -/
structure IsReduction (P Q : Problem) (R : List ℕ → List ℕ) : Prop where
  /-- Instances go to instances. -/
  maps_domain : ∀ x ∈ P.Domain, R x ∈ Q.Domain
  /-- Yes-instances go to yes-instances, and no-instances to no-instances. -/
  correct : ∀ x ∈ P.Domain, (P.Yes x ↔ Q.Yes (R x))

/-- **Step 2 of a reduction: the parameter bound.** The parameter of `R x` is at most a computable
function of the parameter of `x`. -/
def ParamBounded (P Q : Problem) (R : List ℕ → List ℕ) : Prop :=
  ∃ g : ℕ → ℕ, Computable g ∧ ∀ x ∈ P.Domain, Q.param (R x) ≤ g (P.param x)

/-- An **fpt-reduction** [FG06, Definition 2.1]: a reduction with a bounded parameter,
computable in fixed-parameter time (**step 3**) on the instances of `P`. -/
structure IsFptReduction (P Q : Problem) (R : List ℕ → List ℕ) : Prop where
  /-- Construction and correctness. -/
  reduction : IsReduction P Q R
  /-- The parameter bound. -/
  param_bounded : ParamBounded P Q R
  /-- The running time. -/
  fpt_time : FptTimeOn P.Domain P.param R

/-- `P` **fpt-reduces** to `Q`. -/
def FptReduces (P Q : Problem) : Prop := ∃ R, IsFptReduction P Q R

@[inherit_doc] scoped infix:50 " ≤ᶠᵖᵗ " => FptReduces

end Lax496464.WH_A2_FptReductions
end

-- Lax434175.WordProblems
section
namespace Lax434175.WordProblems
end Lax434175.WordProblems

namespace Lax434175.WordProblems.Coding
end Lax434175.WordProblems.Coding
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax496464.WH_B1_Structures
section
namespace Lax496464
end Lax496464

namespace Lax496464.WH_B1_Structures
end Lax496464.WH_B1_Structures

namespace Lax496464.WH_B1_Structures.Structure
end Lax496464.WH_B1_Structures.Structure
end

-- Lax496464.WH_B2_FirstOrder
section
namespace Lax496464.WH_B2_FirstOrder
end Lax496464.WH_B2_FirstOrder

namespace Lax496464.WH_B2_FirstOrder.Alt
end Lax496464.WH_B2_FirstOrder.Alt

namespace Lax496464.WH_B2_FirstOrder.Assignment
end Lax496464.WH_B2_FirstOrder.Assignment

namespace Lax496464.WH_B2_FirstOrder.Formula
end Lax496464.WH_B2_FirstOrder.Formula

namespace Lax496464.WH_B2_FirstOrder.Sat
end Lax496464.WH_B2_FirstOrder.Sat

namespace Lax496464.WH_B2_FirstOrder.Formula.ArityAtMost
end Lax496464.WH_B2_FirstOrder.Formula.ArityAtMost

namespace Lax496464.WH_B2_FirstOrder.Formula.IsPositive
end Lax496464.WH_B2_FirstOrder.Formula.IsPositive

namespace Lax496464.WH_B2_FirstOrder.Formula.IsQF
end Lax496464.WH_B2_FirstOrder.Formula.IsQF

namespace Lax496464.WH_B2_FirstOrder.Formula.NoSetVar
end Lax496464.WH_B2_FirstOrder.Formula.NoSetVar

namespace Lax496464.WH_B2_FirstOrder.Formula.all
end Lax496464.WH_B2_FirstOrder.Formula.all

namespace Lax496464.WH_B2_FirstOrder.Formula.and
end Lax496464.WH_B2_FirstOrder.Formula.and

namespace Lax496464.WH_B2_FirstOrder.Formula.eq
end Lax496464.WH_B2_FirstOrder.Formula.eq

namespace Lax496464.WH_B2_FirstOrder.Formula.ex
end Lax496464.WH_B2_FirstOrder.Formula.ex

namespace Lax496464.WH_B2_FirstOrder.Formula.freeVars
end Lax496464.WH_B2_FirstOrder.Formula.freeVars

namespace Lax496464.WH_B2_FirstOrder.Formula.neg
end Lax496464.WH_B2_FirstOrder.Formula.neg

namespace Lax496464.WH_B2_FirstOrder.Formula.or
end Lax496464.WH_B2_FirstOrder.Formula.or

namespace Lax496464.WH_B2_FirstOrder.Formula.rel
end Lax496464.WH_B2_FirstOrder.Formula.rel

namespace Lax496464.WH_B2_FirstOrder.Formula.setVar
end Lax496464.WH_B2_FirstOrder.Formula.setVar
end

-- Lax496464.WH_B3_LogicProblems
section
namespace Lax496464.WH_B3_LogicProblems
end Lax496464.WH_B3_LogicProblems
end

-- Lax496464.WH_B4_Hierarchies
section
namespace Lax496464.WH_B4_Hierarchies
end Lax496464.WH_B4_Hierarchies
end

-- Lax759944.TuringPolytime
section
namespace Lax759944.TuringPolytime
end Lax759944.TuringPolytime
end

-- Lax496464.WH_F3_NPHard
section
namespace Lax496464
end Lax496464

namespace Lax496464.WH_F3_NPHard
end Lax496464.WH_F3_NPHard
end

-- Lax434175.Results
section
namespace Lax434175.Results

open Lax434175.Problems Lax434175.Kernels Lax434175.Assembly Lax434175.Parameters

open Lax434175.WordProblems Lax434175.Online

open Lax808846.Ram Lax759944.BinaryWordEncoding

open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

/-- A reading of a problem: words of instances, schedules from words, and what
an online scheduler sees. -/
structure PReading (P : Problem) where
  /-- The word encodes the instance. -/
  Encodes : List ℕ → P.Inst → Prop
  /-- The word writes the schedule of the instance. -/
  Decodes : (x : P.Inst) → List ℕ → P.Sched x → Prop
  /-- What is revealed over time. -/
  reveal : Revelation P

/-- A reading of a family. -/
structure Reading {K : Kernel} (F : Family K) where
  /-- The word encodes the instance. -/
  Encodes : (s : Spec F) → List ℕ → Inst F s → Prop
  /-- The word writes the schedule of the instance. -/
  Decodes : (s : Spec F) → (x : Inst F s) → List ℕ → (problem F s).Sched x → Prop
  /-- What is revealed over time. -/
  reveal : (s : Spec F) → Revelation (problem F s)

/-- The reading of the problem of one specification. -/
def Reading.at {K : Kernel} {F : Family K} (R : Reading F) (s : Spec F) :
    PReading (problem F s) :=
  ⟨R.Encodes s, R.Decodes s, R.reveal s⟩

variable {P : Problem} (R : PReading P)

/-- The largest number of a word. -/
def maxEntry (w : List ℕ) : ℕ := w.foldr max 0

/-- The word presents the instance with the threshold. -/
def EncodesDecision (w : List ℕ) (x : P.Inst) (D : ℤ) : Prop :=
  ∃ y, w = y ++ [if D < 0 then 1 else 0, D.natAbs] ∧ R.Encodes y x

/-- The word lengths a program may use on input `u`: `c` times the logarithm of
the length plus the largest number. -/
def WordOk (c : ℕ) (u : List ℕ) (ℓ : ℕ) : Prop := (u.length + maxEntry u + 2) ^ c ≤ 2 ^ ℓ

open Classical in
/-- The answer for an instance and a threshold: `[1]` if some feasible schedule
costs at most the threshold, `[0]` otherwise. -/
noncomputable def verdict (x : P.Inst) (D : ℤ) : List ℕ := if P.Decides x D then [1] else [0]

/-- One program decides the decision version within `T x D` instructions, with no
hidden constant: on every word of an instance `x` with a threshold `D` it writes the
answer within `T x D` steps of the word RAM. -/
def DecidesExact (T : P.Inst → ℤ → ℕ) : Prop :=
  ∃ (p : Program) (c : ℕ), ∀ u x D, EncodesDecision R u x D →
    ∀ ℓ, WordOk c u ℓ → ∃ t ≤ T x D, RunsTo ℓ p (u.length :: u) (verdict x D) t

end Lax434175.Results
end

-- Lax434175.ZooParameters
section
namespace Lax434175.ZooParameters
end Lax434175.ZooParameters

namespace Lax434175.ZooParameters.Parallel
end Lax434175.ZooParameters.Parallel

namespace Lax434175.ZooParameters.Shop
end Lax434175.ZooParameters.Shop
end

-- Lax434175.ResultParameters
section
namespace Lax434175.ResultParameters
end Lax434175.ResultParameters

namespace Lax434175.ResultParameters.Batch
end Lax434175.ResultParameters.Batch

namespace Lax434175.ResultParameters.Cover
end Lax434175.ResultParameters.Cover

namespace Lax434175.ResultParameters.Ops
end Lax434175.ResultParameters.Ops

namespace Lax434175.ResultParameters.Reject
end Lax434175.ResultParameters.Reject

namespace Lax434175.ResultParameters.Batch.windowEnd
end Lax434175.ResultParameters.Batch.windowEnd

namespace Lax434175.ResultParameters.Ops.windowEnd
end Lax434175.ResultParameters.Ops.windowEnd
end

-- Lax434175.StandardReading
section
namespace Lax434175.StandardReading
end Lax434175.StandardReading

namespace Lax434175.StandardReading.Slot
end Lax434175.StandardReading.Slot

namespace Lax434175.StandardReading.expand
end Lax434175.StandardReading.expand
end

-- Lax434175.Propagation
section
namespace Lax434175.Propagation

open Lax434175 Lax434175.Problems Lax434175.Kernels Lax434175.Assembly Lax434175.Results

variable {K : Kernel} {F : Family K} (hF : F.Sound) (R : Reading F)

/-- The reading lifts along `s ≤ t`. -/
def Lifts {s t : Spec F} (h : s.le t) : Prop :=
  (∀ x w, R.Encodes s w x → R.Encodes t w ((lift F hF h).map x)) ∧
    ∀ x w σ, R.Decodes t ((lift F hF h).map x) w σ → R.Decodes s x w σ

variable {hF R}

axiom decidesExact_down {s t : Spec F} {h : s.le t} (hl : Lifts hF R h) {T : Inst F t → ℤ → ℕ} :
    DecidesExact (R.at t) T → DecidesExact (R.at s) fun x D => T ((lift F hF h).map x) D

open Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

variable {s t : Spec F} {h : s.le t}

end Lax434175.Propagation
end
