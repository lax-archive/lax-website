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

end Lax434175.Modules
end

-- Lax434175.Problems
section
namespace Lax434175.Problems.Embedding
end Lax434175.Problems.Embedding

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

/-- Some feasible solution of the instance has cost at most the threshold. -/
def Problem.Decides (P : Problem) (x : P.Inst) (D : ℚ) : Prop :=
  ∃ σ, P.feasible x σ ∧ P.cost x σ ≤ D

/-- The data of a reduction between decision versions: an instance and a
threshold of `A` are mapped to an instance and a threshold of `B`. -/
structure DecisionReduction (A B : Problem) where
  map : A.Inst → ℤ → B.Inst
  threshold : A.Inst → ℤ → ℤ

/-- A reduction is sound if it preserves the answer. -/
def DecisionReduction.Sound {A B : Problem} (r : DecisionReduction A B) : Prop :=
  ∀ x (D : ℤ), A.Decides x D ↔ B.Decides (r.map x D) (r.threshold x D)

/-- The decision version of `A` reduces to that of `B`. -/
def Reducible (A B : Problem) : Prop := ∃ r : DecisionReduction A B, r.Sound

end Lax434175.Problems
end

-- Lax434175.Assembly
section
namespace Lax434175.Assembly.Family.Sound
end Lax434175.Assembly.Family.Sound

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

end Lax434175.Assembly
end

-- Lax434175.Objectives
section
namespace Lax434175.Objectives

open Lax434175.Kernels Lax434175.Modules

inductive Value
  | makespan
  | lmax
  | sumC
  | sumWC
  | sumT
  | sumWT
  | sumU
  | sumWU
  | sumZ
  | sumWZ
  | sumF
  | sumWF
  | fmax
  | maxWF
  | sumWTCommon
  | sumWUWindow (k : ℕ)
  deriving DecidableEq

/-- How the cost is formed from the completion times. -/
inductive Kind
  | maximum
  | tardiness
  | late
  | notJustInTime
  | flow
  | maximumFlow
  deriving DecidableEq

def kind : Value → Kind
  | .makespan | .lmax => .maximum
  | .sumC | .sumWC | .sumT | .sumWT | .sumWTCommon => .tardiness
  | .sumU | .sumWU | .sumWUWindow _ => .late
  | .sumZ | .sumWZ => .notJustInTime
  | .sumF | .sumWF => .flow
  | .fmax | .maxWF => .maximumFlow

/-- Whether the value carries weights. -/
def weighted : Value → Bool
  | .sumWC | .sumWT | .sumWU | .sumWZ | .sumWF | .maxWF | .sumWTCommon | .sumWUWindow _ => true
  | _ => false

/-- Whether the value carries due dates. -/
def hasDueDates : Value → Bool
  | .lmax | .sumT | .sumWT | .sumU | .sumWU | .sumZ | .sumWZ | .sumWTCommon | .sumWUWindow _ => true
  | _ => false

/-- Weights where the value is weighted, due dates where it has them. -/
def Data (K : Kernel) : Value → K.Inst → Type
  | .makespan, _ | .sumC, _ | .sumF, _ | .fmax, _ => Unit
  | .lmax, x | .sumWC, x | .sumT, x | .sumU, x | .sumZ, x | .sumWF, x | .maxWF, x =>
      Fin (K.jobs x) → ℕ
  | .sumWT, x | .sumWU, x | .sumWZ, x | .sumWTCommon, x | .sumWUWindow _, x =>
      (Fin (K.jobs x) → ℕ) × (Fin (K.jobs x) → ℕ)

/-- The weight of a job; `1` when the value is unweighted. -/
def weight {K : Kernel} {x : K.Inst} : (v : Value) → Data K v x → Fin (K.jobs x) → ℕ
  | .sumWC, w | .sumWF, w | .maxWF, w => w
  | .sumWT, d | .sumWU, d | .sumWZ, d | .sumWTCommon, d | .sumWUWindow _, d => d.1
  | .makespan, _ | .lmax, _ | .sumC, _ | .sumT, _ | .sumU, _ | .sumZ, _ | .sumF, _
  | .fmax, _ => fun _ => 1

/-- The due date of a job; `0` when the value has no due dates. -/
def dueDate {K : Kernel} {x : K.Inst} : (v : Value) → Data K v x → Fin (K.jobs x) → ℕ
  | .lmax, d | .sumT, d | .sumU, d | .sumZ, d => d
  | .sumWT, d | .sumWU, d | .sumWZ, d | .sumWTCommon, d | .sumWUWindow _, d => d.2
  | .makespan, _ | .sumC, _ | .sumWC, _ | .sumF, _ | .sumWF, _ | .fmax, _ | .maxWF, _ =>
      fun _ => 0

/-- The cost of a schedule. Subtraction of nonnegative rationals is
truncated, so `C - d` is the tardiness `max(0, C - d)`. -/
def cost {K : Kernel} (v : Value) (x : K.Inst) (d : Data K v x) (σ : K.Sched x) : ℚ :=
  match kind v with
  | .maximum =>
      if h : 0 < K.jobs x then
        Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩
          (fun j => (K.completion x σ j : ℚ) - (dueDate v d j : ℚ))
      else 0
  | .tardiness =>
      ((∑ j, (weight v d j : NNRat) * (K.completion x σ j - (dueDate v d j : NNRat)) : NNRat) : ℚ)
  | .late =>
      ((∑ j, (weight v d j : NNRat) *
        (if (dueDate v d j : NNRat) < K.completion x σ j then 1 else 0) : NNRat) : ℚ)
  | .notJustInTime =>
      ((∑ j, (weight v d j : NNRat) *
        (if K.completion x σ j = (dueDate v d j : NNRat) then 0 else 1) : NNRat) : ℚ)
  | .flow =>
      ((∑ j, (weight v d j : NNRat) * (K.completion x σ j - (K.release x j : NNRat)) : NNRat) : ℚ)
  | .maximumFlow =>
      ((Finset.univ.sup fun j =>
        (weight v d j : NNRat) * (K.completion x σ j - (K.release x j : NNRat)) : NNRat) : ℚ)

/-- The condition on the due dates of the two restricted values. -/
def admits {K : Kernel} : (v : Value) → (x : K.Inst) → Data K v x → Prop
  | .sumWTCommon, _, d => ∃ c, ∀ j, d.2 j = c
  | .sumWUWindow k, x, d => ∀ j, d.2 j ≤ K.release x j + k
  | _, _, _ => True

/-- Comparison of the restrictions on the due dates. -/
def restrictionLe : Value → Value → Bool
  | .sumWTCommon, .sumWTCommon => true
  | .sumWUWindow k, .sumWUWindow l => decide (k ≤ l)
  | _, .sumWTCommon => false
  | _, .sumWUWindow _ => false
  | _, _ => true

def le (v w : Value) : Bool :=
  decide (kind v = kind w) && (!weighted v || weighted w) && (!hasDueDates v || hasDueDates w) &&
    restrictionLe v w

def embed {K : Kernel} : {v w : Value} → le v w = true → (x : K.Inst) → Data K v x → Data K w x
  | _, .makespan, _, _, _ | _, .sumC, _, _, _ | _, .sumF, _, _, _ | _, .fmax, _, _, _ => ()
  | v, .sumWC, _, _, d | v, .sumWF, _, _, d | v, .maxWF, _, _, d => weight v d
  | v, .lmax, _, _, d | v, .sumT, _, _, d | v, .sumU, _, _, d | v, .sumZ, _, _, d => dueDate v d
  | v, .sumWT, _, _, d | v, .sumWU, _, _, d | v, .sumWZ, _, _, d | v, .sumWTCommon, _, _, d
  | v, .sumWUWindow _, _, _, d => (weight v d, dueDate v d)

/-- The objective field over a kernel. -/
def objective (K : Kernel) : Objective K where
  Value := Value
  Data := Data K
  admits := admits
  cost := cost
  le := le
  embed := embed

end Lax434175.Objectives
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

/-- The family of given constraint modules with the completion-time
objectives. -/
def family {K : Kernel} (Name : Type) (module : Name → Module K) : Family K where
  ModuleName := Name
  module := module
  objective := Objectives.objective K

variable {K : Kernel} {Name : Type} {module : Name → Module K}

/-- The specification with given module values and a given objective. -/
def withObjective (values : (i : Name) → (module i).Value) (objective : Objectives.Value) :
    Spec (family Name module) where
  module := values
  objective := objective

/-- The objective of a specification. -/
def objectiveOf (s : Spec (family Name module)) : Objectives.Value := s.objective

/-- The specification `s` reduces to `t`: field by field, possibly after one
of the threshold steps. -/
def Reduces (s t : Spec (family Name module)) : Prop :=
  s.le t ∨
  ((objectiveOf s = .makespan ∨ objectiveOf s = .lmax) ∧
    (withObjective s.module .sumU : Spec (family Name module)).le t) ∨
  ((objectiveOf s = .makespan ∨ objectiveOf s = .lmax ∨ objectiveOf s = .sumF) ∧
    (withObjective s.module .sumT : Spec (family Name module)).le t) ∨
  (objectiveOf s = .sumWF ∧ (withObjective s.module .sumWT : Spec (family Name module)).le t)

axiom reducible_of_reduces (sound : ∀ i, (module i).Sound) {s t : Spec (family Name module)} :
    Reduces s t → Reducible (problem _ s) (problem _ t)

end Lax434175.Thresholds
end
