-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.NNRat.BigOperators
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

open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly

open Lax434175

variable {K : Kernel} {Name : Type} {module : Name → Module K}

/-- In every schedule that is feasible for the kernel and the modules, every
job completes no earlier than its release date. -/
def ReleaseRespected (values : (i : Name) → (module i).Value) : Prop :=
  ∀ (x : K.Inst) (data : (i : Name) → (module i).Data (values i) x) (σ : K.Sched x),
    (∀ i, (module i).admits (values i) x (data i)) → K.feasible x σ →
    (∀ i, (module i).constraint (values i) x (data i) σ) →
    ∀ j, (K.release x j : NNRat) ≤ K.completion x σ j

end Lax434175.Thresholds
end
