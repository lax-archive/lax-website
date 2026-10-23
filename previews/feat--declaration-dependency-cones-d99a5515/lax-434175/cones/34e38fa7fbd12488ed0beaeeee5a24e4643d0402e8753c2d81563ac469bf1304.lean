-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
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

-- Lax434175.Batching
section
namespace Lax434175.Batching.Mode
end Lax434175.Batching.Mode

namespace Lax434175.Batching.length
end Lax434175.Batching.length

namespace Lax434175.Batching.Capacity.Data
end Lax434175.Batching.Capacity.Data

namespace Lax434175.Batching.Capacity.bound
end Lax434175.Batching.Capacity.bound

namespace Lax434175.Batching.Capacity.embed
end Lax434175.Batching.Capacity.embed

namespace Lax434175.Batching.Capacity.le
end Lax434175.Batching.Capacity.le

namespace Lax434175.Batching.Mode.parallel
end Lax434175.Batching.Mode.parallel

namespace Lax434175.Batching.Mode.serial
end Lax434175.Batching.Mode.serial

namespace Lax434175.Batching.ProcessingTimes.holds
end Lax434175.Batching.ProcessingTimes.holds

namespace Lax434175.Batching.ProcessingTimes.rank
end Lax434175.Batching.ProcessingTimes.rank

namespace Lax434175.Batching

open Lax434175.Kernels Lax434175.Modules

structure Inst where
  jobs : ℕ
  p : Fin jobs → ℕ
  /-- The release date of a job. -/
  r : Fin jobs → ℕ
  /-- The setup time before every batch. -/
  setup : ℕ

structure Sched (x : Inst) where
  /-- The number of the batch of a job. -/
  batch : Fin x.jobs → ℕ
  /-- The start time of a batch. -/
  start : ℕ → ℕ

/-- The jobs of a batch. -/
def members {x : Inst} (σ : Sched x) (k : ℕ) : Finset (Fin x.jobs) :=
  Finset.univ.filter (fun j => σ.batch j = k)

inductive Capacity
  | unbounded
  | bounded
  | sizes

inductive ProcessingTimes
  | unit
  | equal
  | arbitrary

end Lax434175.Batching
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
namespace Lax434175.BatchFamily.FieldName
end Lax434175.BatchFamily.FieldName

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

namespace Lax434175.BatchFamily

open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly

open Lax434175

open Lax434175.Batching (Inst Capacity ProcessingTimes members)

/-- A batch schedule with the processing time of every batch. -/
structure Sched (x : Inst) where
  /-- The number of the batch of a job. -/
  batch : Fin x.jobs → ℕ
  /-- The start time of a batch. -/
  start : ℕ → ℕ
  /-- The processing time of a batch. -/
  length : ℕ → ℕ

/-- The completion time of a batch. -/
def finish {x : Inst} (σ : Sched x) (k : ℕ) : ℕ := σ.start k + σ.length k

end Lax434175.BatchFamily
end
