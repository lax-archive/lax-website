-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Data.List.Basic
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Set.Basic
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
namespace Lax434175.Problems.DecisionReduction
end Lax434175.Problems.DecisionReduction

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

end Lax434175.Assembly
end

-- Lax434175.ParallelMachines
section
namespace Lax434175.ParallelMachines

open Lax434175.Kernels Lax434175.Modules

structure Inst where
  jobs : ℕ
  machines : ℕ
  /-- The processing time of a job on a machine. -/
  p : Fin jobs → Fin machines → ℕ
  /-- The release date of a job. -/
  r : Fin jobs → ℕ

/-- The time a job needs when it occupies a set of machines. -/
def duration (x : Inst) (j : Fin x.jobs) (S : Finset (Fin x.machines)) : ℕ :=
  S.sup (x.p j)

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

inductive ProcessingTimes
  | unit
  | equal
  | oneOrTwo
  | arbitrary
  deriving DecidableEq

/-- The instances of a processing-time restriction. -/
def ProcessingTimes.holds : ProcessingTimes → Inst → Prop
  | .unit, x => ∀ j i, x.p j i = 1
  | .equal, x => ∃ p, ∀ j i, x.p j i = p
  | .oneOrTwo, x => ∀ j i, x.p j i = 1 ∨ x.p j i = 2
  | .arbitrary, _ => True

def ProcessingTimes.le : ProcessingTimes → ProcessingTimes → Bool
  | _, .arbitrary => true
  | .unit, _ => true
  | v, w => decide (v = w)

/-- The processing-time field. -/
def processingTimes (M : Model) : Module M.kernel :=
  Module.ofRestriction ProcessingTimes (fun v x => v.holds (M.inst x)) ProcessingTimes.le

/-- The number of machines, a parameter of every machine model. -/
def machines (M : Model) : M.kernel.Inst → ℕ := fun x => (M.inst x).machines

end Lax434175.ParallelMachines
end

-- Lax434175.CommunicationDelays
section
namespace Lax434175.CommunicationDelays

open Lax434175.Kernels Lax434175.Modules Lax434175.ParallelMachines

inductive Value
  | none
  | unit
  | general

/-- The data of a value. -/
def Data : Value → Inst → Type
  | .none, _ => Unit
  | .unit, x => Fin x.jobs → Fin x.jobs → Prop
  | .general, x => Fin x.jobs → Fin x.jobs → ℕ → Prop

/-- `view v d i j c`: the pair `(i, j)` has the delay `c`. -/
def view {x : Inst} : (v : Value) → Data v x → Fin x.jobs → Fin x.jobs → ℕ → Prop
  | .none, _ => fun _ _ _ => False
  | .unit, r => fun i j c => r i j ∧ c = 1
  | .general, d => d

def le : Value → Value → Bool
  | .none, _ => true
  | .unit, .none => false
  | .unit, _ => true
  | .general, .general => true
  | .general, _ => false

def embed : {v w : Value} → le v w = true → (x : Inst) → Data v x → Data w x
  | _, .none, _, _, _ => ()
  | .none, .unit, _, _, _ => fun _ _ => False
  | .unit, .unit, _, _, d => d
  | v, .general, _, _, d => view v d
  | .general, .unit, h, _, _ => absurd h Bool.false_ne_true

/-- The communication-delay field of a machine model. -/
def module (M : Model) : Module M.kernel where
  Value := Value
  Data v x := Data v (M.inst x)
  admits _ _ _ := True
  constraint v x d σ := ∀ i j c, view v d i j c → ∀ S S', M.uses x σ i S → M.uses x σ j S' →
    S ≠ S' →
    (M.kernel.completion x σ (Fin.cast (M.jobs_eq x).symm i) : ℚ) + (c : ℚ) ≤
      (M.kernel.start x σ (Fin.cast (M.jobs_eq x).symm j) : ℚ)
  le := le
  embed h x d := embed h (M.inst x) d

end Lax434175.CommunicationDelays
end

-- Lax434175.Counts
section
namespace Lax434175.Counts

open Lax434175.Kernels Lax434175.Modules

inductive Bound
  | atMost (k : ℕ)
  | constant
  | unlimited
  | atMostJobsPlusOne
  | any

/-- The numbers admitted by a bound, given the number of jobs. -/
def Bound.holds : Bound → (jobs count : ℕ) → Prop
  | .atMost k, _, n => n ≤ k
  | .constant, _, _ => True
  | .unlimited, jobs, n => jobs ≤ n
  | .atMostJobsPlusOne, jobs, n => n ≤ jobs + 1
  | .any, _, _ => True

def Bound.le : Bound → Bound → Bool
  | _, .any => true
  | .atMost k, .atMost l => decide (k ≤ l)
  | .atMost _, .constant => true
  | .constant, .constant => true
  | .unlimited, .unlimited => true
  | .atMostJobsPlusOne, .atMostJobsPlusOne => true
  | _, _ => false

/-- The numbers admitted by a bound, given the number of jobs and the least
number that a bound `at most k` admits. -/
def Bound.admits (least : ℕ) (v : Bound) (jobs n : ℕ) : Prop :=
  v.holds jobs n ∧ ∀ k, v = .atMost k → least ≤ n

/-- The bound field of a count; a bound `at most k` admits the counts from
`least` to `k`. -/
def module (K : Kernel) (count : K.Inst → ℕ) (least : ℕ := 0) : Module K :=
  Module.ofRestriction Bound (fun v x => v.admits least (K.jobs x) (count x)) Bound.le

end Lax434175.Counts
end

-- Lax434175.Deadlines
section
namespace Lax434175.Deadlines

open Lax434175.Kernels Lax434175.Modules

inductive Value
  | none
  | common
  | deadlines

/-- No data without deadlines; one deadline per job with them. -/
def Data (K : Kernel) : Value → K.Inst → Type
  | .none, _ => Unit
  | .common, _ => ℕ∞
  | .deadlines, x => Fin (K.jobs x) → ℕ∞

/-- The deadline of a job; `∞` when the field is absent. -/
def view {K : Kernel} {x : K.Inst} : (v : Value) → Data K v x → Fin (K.jobs x) → ℕ∞
  | .none, _ => fun _ => ⊤
  | .common, d => fun _ => d
  | .deadlines, d => d

def le : Value → Value → Bool
  | .deadlines, .none | .deadlines, .common | .common, .none => false
  | _, _ => true

def embed {K : Kernel} : {v w : Value} → le v w = true → (x : K.Inst) → Data K v x → Data K w x
  | _, .none, _, _, _ => ()
  | .none, .common, _, _, _ => (⊤ : ℕ∞)
  | .common, .common, _, _, d => d
  | v, .deadlines, _, _, d => view v d
  | .deadlines, .common, h, _, _ => absurd h Bool.false_ne_true

/-- A time is within a deadline. -/
def Within (c : NNRat) : ℕ∞ → Prop
  | none => True
  | some d => c ≤ (d : NNRat)

/-- The deadline field over a kernel. -/
def module (K : Kernel) : Module K where
  Value := Value
  Data := Data K
  admits _ _ _ := True
  constraint v x d σ := ∀ j, Within (K.completion x σ j) (view v d j)
  le := le
  embed := embed

end Lax434175.Deadlines
end

-- Lax434175.ForbiddenTimes
section
namespace Lax434175.ForbiddenTimes

open Lax434175.Kernels Lax434175.Modules

inductive Value
  | none
  | forbidden

/-- No data without forbidden times; a list of points in time with them. -/
def Data : Value → Type
  | .none => Unit
  | .forbidden => List ℕ

/-- The forbidden times; none when the field is absent. -/
def view : (v : Value) → Data v → List ℕ
  | .none, _ => []
  | .forbidden, l => l

def le : Value → Value → Bool
  | .forbidden, .none => false
  | _, _ => true

def embed : {v w : Value} → le v w = true → Data v → Data w
  | _, .none, _, _ => ()
  | v, .forbidden, _, d => view v d

/-- The forbidden-times field over a kernel. -/
def module (K : Kernel) : Module K where
  Value := Value
  Data v _ := Data v
  admits _ _ _ := True
  constraint v x d σ := ∀ t ∈ view v d, ∀ j,
    K.start x σ j ≠ (t : NNRat) ∧ K.completion x σ j ≠ (t : NNRat)
  le := le
  embed h _ d := embed h d

inductive Encoding
  | standard
  | highMultiplicity
  deriving DecidableEq

/-- The encoding field over a kernel. -/
def encoding (K : Kernel) : Module K :=
  Module.ofRestriction Encoding (fun _ _ => True)
    (fun v w => decide (v = .standard ∨ v = w))

end Lax434175.ForbiddenTimes
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

/-- The machine-set field. -/
def module (M : Model) : Module M.kernel where
  Value := Value
  Data v x := Data v (M.inst x)
  admits _ _ _ := True
  constraint v x d σ := ∀ j S, M.uses x σ j S → view v d j S
  le := le
  embed h x d := embed h (M.inst x) d

end Lax434175.MachineSets
end

-- Lax434175.Nonpreemptive
section
namespace Lax434175.Nonpreemptive

open Lax434175.Kernels Lax434175.ParallelMachines

structure Sched (x : Inst) where
  machines : Fin x.jobs → Finset (Fin x.machines)
  start : Fin x.jobs → ℕ

def completion (x : Inst) (σ : Sched x) (j : Fin x.jobs) : ℕ :=
  σ.start j + duration x j (σ.machines j)

/-- Every job occupies some machine, and two distinct jobs that share a
machine do not overlap. -/
def feasible (x : Inst) (σ : Sched x) : Prop :=
  (∀ j, (σ.machines j).Nonempty) ∧
  ∀ i j, i ≠ j → ¬ Disjoint (σ.machines i) (σ.machines j) →
    completion x σ i ≤ σ.start j ∨ completion x σ j ≤ σ.start i

/-- The kernel of non-preemptive scheduling on parallel machines. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible := feasible
  start _ σ j := (σ.start j : NNRat)
  completion x σ j := (completion x σ j : NNRat)

/-- Non-preemptive scheduling as a machine model. -/
def model : Model where
  kernel := kernel
  inst x := x
  jobs_eq _ := rfl
  uses _ σ j S := Sched.machines σ j = S

end Lax434175.Nonpreemptive
end

-- Lax434175.Precedence
section
namespace Lax434175.Precedence

open Lax434175.Kernels Lax434175.Modules

inductive Order
  | none
  | chains
  | intree
  | outtree
  | tree
  | opposingForest
  | seriesParallel
  | divideAndConquer
  | intervalOrder
  | quasiInterval
  | overInterval
  | aOrder
  | levelOrder
  | boundedHeight
  | dimensionTwo
  | boundedDimension
  | prec
  deriving DecidableEq

/-- No data without precedence constraints; a relation on the jobs with them. -/
def Order.Data (n : ℕ) : Order → Type
  | .none => Unit
  | _ => Fin n → Fin n → Prop

/-- The precedence relation; empty when the class is none. -/
def Order.view {n : ℕ} : (v : Order) → v.Data n → Fin n → Fin n → Prop
  | .none, _ => fun _ _ => False
  | .chains, r | .intree, r | .outtree, r | .tree, r | .opposingForest, r
  | .seriesParallel, r | .divideAndConquer, r | .intervalOrder, r | .levelOrder, r | .boundedHeight, r
  | .quasiInterval, r | .overInterval, r | .aOrder, r
  | .dimensionTwo, r
  | .boundedDimension, r | .prec, r => r

/-- Every job has at most one successor. -/
def AtMostOneSuccessor {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ i j k, r i j → r i k → j = k

/-- Every job has at most one predecessor. -/
def AtMostOnePredecessor {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ i j k, r j i → r k i → j = k

/-- The jobs split into an intree part and an outtree part without arcs
between them. -/
def OpposingForest {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∃ inPart : Fin n → Prop, (∀ i j, r i j → (inPart i ↔ inPart j)) ∧
    (∀ i j k, inPart i → r i j → r i k → j = k) ∧
    (∀ i j k, ¬ inPart i → r j i → r k i → j = k)

/-- No four jobs are related exactly by `a ≺ c`, `b ≺ c`, `b ≺ d`. -/
def SeriesParallel {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ a b c d, Relation.TransGen r a c → Relation.TransGen r b c → Relation.TransGen r b d →
    Relation.TransGen r a d ∨ Relation.TransGen r a b ∨ Relation.TransGen r b a ∨
      Relation.TransGen r c d ∨ Relation.TransGen r d c

/-- The arcs among a set of jobs form a divide-and-conquer graph. -/
inductive DivideAndConquer {n : ℕ} (r : Fin n → Fin n → Prop) : Finset (Fin n) → Prop
  | single (v : Fin n) : ¬ r v v → DivideAndConquer r {v}
  | compose (s t : Fin n) (parts : List (Finset (Fin n))) :
      s ≠ t → parts ≠ [] → (∀ P ∈ parts, s ∉ P ∧ t ∉ P) → parts.Pairwise Disjoint →
      (∀ P ∈ parts, DivideAndConquer r P) →
      (∀ a b, (a = s ∨ a = t ∨ ∃ P ∈ parts, a ∈ P) → (b = s ∨ b = t ∨ ∃ P ∈ parts, b ∈ P) →
        (r a b ↔ (∃ P ∈ parts, a ∈ P ∧ b ∈ P ∧ r a b) ∨ (a = s ∧ ∃ P ∈ parts, b ∈ P) ∨
          (b = t ∧ ∃ P ∈ parts, a ∈ P))) →
      DivideAndConquer r (parts.foldr (· ∪ ·) {s, t})

/-- `a ≺ b` and `c ≺ d` imply `a ≺ d` or `c ≺ b`. -/
def IntervalOrder {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ a b c d, Relation.TransGen r a b → Relation.TransGen r c d →
    Relation.TransGen r a d ∨ Relation.TransGen r c b

/-- Five different jobs are related exactly by the pairs of a pattern. -/
def Contains {n : ℕ} (r : Fin n → Fin n → Prop) (pattern : List (Fin 5 × Fin 5)) : Prop :=
  ∃ f : Fin 5 → Fin n, Function.Injective f ∧
    ∀ a b, Relation.TransGen r (f a) (f b) ↔ (a, b) ∈ pattern

/-- Two unrelated pairs, the first job of one having a further successor. -/
def patternOut : List (Fin 5 × Fin 5) := [(0, 1), (2, 3), (2, 4)]

/-- The reverse of `patternOut`. -/
def patternIn : List (Fin 5 × Fin 5) := [(1, 0), (3, 2), (4, 2)]

/-- The third pattern forbidden in a quasi-interval order. -/
def patternThird : List (Fin 5 × Fin 5) := [(0, 1), (0, 3), (2, 3), (2, 4), (4, 3)]

/-- Neither `patternOut` nor its reverse occurs. -/
def OverInterval {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ¬ Contains r patternOut ∧ ¬ Contains r patternIn

/-- An over-interval order in which `patternThird` does not occur. -/
def QuasiInterval {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  OverInterval r ∧ ¬ Contains r patternThird

/-- Moukrim and Quilliot's property `Q_m`: for two sets of at most `m` pairwise
unrelated jobs, at most `m` jobs of their union have a predecessor in the union,
and at most `m` have a successor in the union. -/
def AOrder {n : ℕ} (m : ℕ) (r : Fin n → Fin n → Prop) : Prop :=
  ∀ A B : Finset (Fin n), (∀ x ∈ A, ∀ y ∈ A, ¬ Relation.TransGen r x y) →
    (∀ x ∈ B, ∀ y ∈ B, ¬ Relation.TransGen r x y) → A.card ≤ m → B.card ≤ m →
    ∀ U ⊆ A ∪ B,
      ((∀ x ∈ U, ∃ y ∈ A ∪ B, Relation.TransGen r y x) → U.card ≤ m) ∧
      ((∀ x ∈ U, ∃ y ∈ A ∪ B, Relation.TransGen r x y) → U.card ≤ m)

/-- A path of `l` arcs starts from the job. -/
def HasPath {n : ℕ} (r : Fin n → Fin n → Prop) : ℕ → Fin n → Prop
  | 0, _ => True
  | l + 1, v => ∃ w, r v w ∧ HasPath r l w

/-- The longest path of arcs starting from the job has `l` arcs. -/
def HasLevel {n : ℕ} (r : Fin n → Fin n → Prop) (v : Fin n) (l : ℕ) : Prop :=
  HasPath r l v ∧ ¬ HasPath r (l + 1) v

/-- Every job of level `l + 1` precedes every job of level `l`. -/
def LevelOrder {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  ∀ u v l, HasLevel r u (l + 1) → HasLevel r v l → Relation.TransGen r u v

/-- The jobs can be placed in `k`-dimensional space such that, for different
jobs, `i ≺ j` exactly if every coordinate of `i` is at most that of `j`. -/
def HasDimension {n : ℕ} (k : ℕ) (r : Fin n → Fin n → Prop) : Prop :=
  ∃ f : Fin n → Fin k → ℚ, ∀ i j, i ≠ j → (Relation.TransGen r i j ↔ ∀ c, f i c ≤ f j c)

/-- The relations of a class, for a number `m` of machines. -/
def Order.InClass {n : ℕ} (m : ℕ) : Order → (Fin n → Fin n → Prop) → Prop
  | .none, r => ∀ i j, ¬ r i j
  | .chains, r => AtMostOneSuccessor r ∧ AtMostOnePredecessor r
  | .intree, r => AtMostOneSuccessor r
  | .outtree, r => AtMostOnePredecessor r
  | .tree, r => AtMostOneSuccessor r ∨ AtMostOnePredecessor r
  | .opposingForest, r => OpposingForest r
  | .seriesParallel, r => SeriesParallel r
  | .divideAndConquer, r => DivideAndConquer r Finset.univ
  | .intervalOrder, r => IntervalOrder r
  | .quasiInterval, r => QuasiInterval r
  | .overInterval, r => OverInterval r
  | .aOrder, r => AOrder m r
  | .levelOrder, r => LevelOrder r
  | .boundedHeight, _ => True
  | .dimensionTwo, r => HasDimension 2 r
  | .boundedDimension, r => ∃ k, HasDimension k r
  | .prec, _ => True

def Order.le : Order → Order → Bool
  | _, .prec => true
  | .none, .divideAndConquer => false
  | .none, _ => true
  | .chains, .chains | .chains, .intree | .chains, .outtree | .chains, .tree
  | .chains, .opposingForest => true
  | .intree, .intree | .intree, .tree | .intree, .opposingForest => true
  | .outtree, .outtree | .outtree, .tree | .outtree, .opposingForest => true
  | .tree, .tree | .tree, .opposingForest => true
  | .chains, .seriesParallel | .intree, .seriesParallel | .outtree, .seriesParallel
  | .tree, .seriesParallel | .opposingForest, .seriesParallel => true
  | .chains, .dimensionTwo | .intree, .dimensionTwo | .outtree, .dimensionTwo
  | .tree, .dimensionTwo | .opposingForest, .dimensionTwo => true
  | .chains, .boundedDimension | .intree, .boundedDimension | .outtree, .boundedDimension
  | .tree, .boundedDimension | .opposingForest, .boundedDimension => true
  | .dimensionTwo, .boundedDimension => true
  | .intervalOrder, .quasiInterval | .intervalOrder, .overInterval | .intervalOrder, .aOrder
  | .quasiInterval, .overInterval => true
  | .seriesParallel, .dimensionTwo | .seriesParallel, .boundedDimension => true
  | v, w => decide (v = w)

def Order.embed {n : ℕ} : {v w : Order} → Order.le v w = true → v.Data n → w.Data n
  | _, .none, _, _ => ()
  | v, .chains, _, d | v, .intree, _, d | v, .outtree, _, d | v, .tree, _, d
  | v, .opposingForest, _, d | v, .seriesParallel, _, d | v, .divideAndConquer, _, d
  | v, .intervalOrder, _, d | v, .quasiInterval, _, d | v, .overInterval, _, d | v, .aOrder, _, d
  | v, .levelOrder, _, d
  | v, .boundedHeight, _, d | v, .dimensionTwo, _, d | v, .boundedDimension, _, d
  | v, .prec, _, d => v.view d

inductive Lags
  | zero
  | unit
  | constant
  | constantNonpositive
  | constantPositive
  | arbitrary
  | arbitraryNonpositive
  | arbitraryPositive
  deriving DecidableEq

/-- The data of a kind of lags. -/
def Lags.Data (n : ℕ) : Lags → Type
  | .zero | .unit => Unit
  | .constant | .constantNonpositive | .constantPositive => ℤ
  | .arbitrary | .arbitraryNonpositive | .arbitraryPositive => Fin n → Fin n → ℤ

/-- The lag between two jobs. -/
def Lags.view {n : ℕ} : (v : Lags) → v.Data n → Fin n → Fin n → ℤ
  | .zero, _ => fun _ _ => 0
  | .unit, _ => fun _ _ => 1
  | .constant, l | .constantNonpositive, l | .constantPositive, l => fun _ _ => l
  | .arbitrary, l | .arbitraryNonpositive, l | .arbitraryPositive, l => l

/-- The sign condition of a kind of lags. -/
def Lags.Admits {n : ℕ} : Lags → (Fin n → Fin n → ℤ) → Prop
  | .constantNonpositive, l | .arbitraryNonpositive, l => ∀ i j, l i j ≤ 0
  | .constantPositive, l | .arbitraryPositive, l => ∀ i j, 0 < l i j
  | _, _ => True

def Lags.le : Lags → Lags → Bool
  | .zero, .zero | .zero, .constant | .zero, .constantNonpositive | .zero, .arbitrary
  | .zero, .arbitraryNonpositive => true
  | .unit, .unit | .unit, .constant | .unit, .constantPositive | .unit, .arbitrary
  | .unit, .arbitraryPositive => true
  | .constant, .constant | .constant, .arbitrary => true
  | .constantNonpositive, .constantNonpositive | .constantNonpositive, .constant
  | .constantNonpositive, .arbitraryNonpositive | .constantNonpositive, .arbitrary => true
  | .constantPositive, .constantPositive | .constantPositive, .constant
  | .constantPositive, .arbitraryPositive | .constantPositive, .arbitrary => true
  | .arbitrary, .arbitrary => true
  | .arbitraryNonpositive, .arbitraryNonpositive | .arbitraryNonpositive, .arbitrary => true
  | .arbitraryPositive, .arbitraryPositive | .arbitraryPositive, .arbitrary => true
  | _, _ => false

def Lags.embed {n : ℕ} : {v w : Lags} → Lags.le v w = true → v.Data n → w.Data n
  | _, .zero, _, _ | _, .unit, _, _ => ()
  | .constant, .constant, _, l | .constantNonpositive, .constant, _, l
  | .constantPositive, .constant, _, l
  | .constantNonpositive, .constantNonpositive, _, l
  | .constantPositive, .constantPositive, _, l => l
  | .zero, .constant, _, _ | .zero, .constantNonpositive, _, _ => (0 : ℤ)
  | .unit, .constant, _, _ | .unit, .constantPositive, _, _ => (1 : ℤ)
  | v, .arbitrary, _, d | v, .arbitraryNonpositive, _, d | v, .arbitraryPositive, _, d =>
      v.view d
  | .zero, .constantPositive, h, _ | .unit, .constantNonpositive, h, _
  | .constant, .constantNonpositive, h, _ | .constant, .constantPositive, h, _
  | .constantNonpositive, .constantPositive, h, _
  | .constantPositive, .constantNonpositive, h, _
  | .arbitrary, .constant, h, _ | .arbitrary, .constantNonpositive, h, _
  | .arbitrary, .constantPositive, h, _ | .arbitraryNonpositive, .constant, h, _
  | .arbitraryNonpositive, .constantNonpositive, h, _
  | .arbitraryNonpositive, .constantPositive, h, _ | .arbitraryPositive, .constant, h, _
  | .arbitraryPositive, .constantNonpositive, h, _
  | .arbitraryPositive, .constantPositive, h, _ => absurd h Bool.false_ne_true

/-- A value of the field: a class of relations and a kind of lags. -/
structure Value where
  order : Order
  lags : Lags := .zero

/-- No precedence constraints. -/
def Value.none : Value := ⟨.none, .zero⟩

/-- The field of precedence constraints with time lags over a kernel with a
number of machines. -/
def module (K : Kernel) (machines : K.Inst → ℕ) : Module K where
  Value := Value
  Data v x := v.order.Data (K.jobs x) × v.lags.Data (K.jobs x)
  admits v x d := v.order.InClass (machines x) (v.order.view d.1) ∧ v.lags.Admits (v.lags.view d.2)
  constraint v x d σ := ∀ i j, v.order.view d.1 i j →
    (K.completion x σ i : ℚ) + (v.lags.view d.2 i j : ℚ) ≤ (K.start x σ j : ℚ)
  le v w := Order.le v.order w.order && Lags.le v.lags w.lags
  embed {v w} h _ d :=
    (Order.embed (v := v.order) (w := w.order) (Bool.and_eq_true_iff.mp h).1 d.1,
      Lags.embed (v := v.lags) (w := w.lags) (Bool.and_eq_true_iff.mp h).2 d.2)

end Lax434175.Precedence
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

-- Lax434175.ReleaseDates
section
namespace Lax434175.ReleaseDates

open Lax434175.Kernels Lax434175.Modules

inductive Value
  | none
  | releaseDates
  | online
  deriving DecidableEq

/-- The instances of a value. -/
def Value.holds (K : Kernel) : Value → K.Inst → Prop
  | .none, x => ∀ j, K.release x j = 0
  | .releaseDates, _ => True
  | .online, _ => True

def le : Value → Value → Bool
  | .none, .releaseDates => true
  | v, w => decide (v = w)

/-- The release-date field over a kernel. -/
def module (K : Kernel) : Module K where
  Value := Value
  Data _ _ := Unit
  admits v x _ := v.holds K x
  constraint _ x _ σ := ∀ j, (K.release x j : NNRat) ≤ K.start x σ j
  le := le
  embed _ _ _ := ()

end Lax434175.ReleaseDates
end

-- Lax434175.Restarts
section
namespace Lax434175.Restarts
end Lax434175.Restarts
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

-- Lax434175.Servers
section
namespace Lax434175.Servers

open Lax434175.Kernels Lax434175.Modules

inductive Value
  | none
  | unit
  | equal
  | arbitrary
  deriving DecidableEq

/-- Setup times of `n` items; no data without a server. -/
def Data (Item : Type) : Value → Type
  | .none => Unit
  | .unit | .equal | .arbitrary => Item → ℕ

/-- The setup times, where there is a server. -/
def view {Item : Type} : (v : Value) → Data Item v → Option (Item → ℕ)
  | .none, _ => Option.none
  | .unit, s | .equal, s | .arbitrary, s => some s

/-- The condition on the setup times. -/
def Admits {Item : Type} : (v : Value) → Data Item v → Prop
  | .unit, s => ∀ a, s a = 1
  | .equal, s => ∃ c, ∀ a, s a = c
  | _, _ => True

def le : Value → Value → Bool
  | .unit, .unit | .unit, .equal | .unit, .arbitrary => true
  | .equal, .equal | .equal, .arbitrary => true
  | .arbitrary, .arbitrary => true
  | .none, .none => true
  | _, _ => false

def embed {Item : Type} : {v w : Value} → le v w = true → Data Item v → Data Item w
  | .none, .none, _, _ => ()
  | .unit, .unit, _, s | .unit, .equal, _, s | .unit, .arbitrary, _, s
  | .equal, .equal, _, s | .equal, .arbitrary, _, s | .arbitrary, .arbitrary, _, s => s
  | .none, .unit, h, _ | .none, .equal, h, _ | .none, .arbitrary, h, _
  | .unit, .none, h, _ | .equal, .none, h, _ | .equal, .unit, h, _
  | .arbitrary, .none, h, _ | .arbitrary, .unit, h, _ | .arbitrary, .equal, h, _ =>
      absurd h Bool.false_ne_true

/-- The server constraints for items with given start and completion times,
release dates of their setups, setup times, and a relation "share a
machine". -/
def Served {Item : Type} (start completion release : Item → ℚ)
    (shares : Item → Item → Prop) (s : Item → ℕ) : Prop :=
  (∀ a, release a + s a ≤ start a) ∧
  (∀ a b, a ≠ b → start a + s b ≤ start b ∨ start b + s a ≤ start a) ∧
  ∀ a b, a ≠ b → shares a b → completion a + s b ≤ start b ∨ completion b + s a ≤ start a

/-- The server field of a machine model on parallel machines. -/
def parallel (M : ParallelMachines.Model) : Module M.kernel where
  Value := Value
  Data v x := Data (Fin (M.kernel.jobs x)) v
  admits v _ d := Admits v d
  constraint v x d σ := ∀ s, view v d = some s →
    Served (fun j => (M.kernel.start x σ j : ℚ)) (fun j => (M.kernel.completion x σ j : ℚ))
      (fun j => (M.kernel.release x j : ℚ)) (fun i j => ∃ S S', M.uses x σ (Fin.cast (M.jobs_eq x) i) S ∧
        M.uses x σ (Fin.cast (M.jobs_eq x) j) S' ∧ ¬ Disjoint S S') s
  le := le
  embed h _ d := embed h d

end Lax434175.Servers
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

end Lax434175.Thresholds
end

-- Lax434175.ParallelProblems
section
namespace Lax434175.ParallelProblems

open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly

open Lax434175

/-- The constraint fields of the family. -/
inductive FieldName
  | environment
  | machineCount
  | jobCount
  | processingTimes
  | machineSets
  | releaseDates
  | deadlines
  | precedence
  | communicationDelays
  | server
  | forbiddenTimes
  | encoding
  deriving DecidableEq

/-- The problems of a machine model on parallel machines. -/
abbrev family (M : ParallelMachines.Model) : Family M.kernel :=
  Thresholds.family FieldName fun
    | .environment => ParallelMachines.environment M
    | .machineCount => Counts.module _ (ParallelMachines.machines M) 1
    | .jobCount => Counts.module _ M.kernel.jobs
    | .processingTimes => ParallelMachines.processingTimes M
    | .machineSets => MachineSets.module M
    | .releaseDates => ReleaseDates.module _
    | .deadlines => Deadlines.module _
    | .precedence => Precedence.module _ (ParallelMachines.machines M)
    | .communicationDelays => CommunicationDelays.module M
    | .server => Servers.parallel M
    | .forbiddenTimes => ForbiddenTimes.module _
    | .encoding => ForbiddenTimes.encoding _

/-- The specification `α | β | γ` in a machine model. -/
def spec (M : ParallelMachines.Model) (environment : ParallelMachines.Environment)
    (machineCount : Counts.Bound := .any)
    (jobCount : Counts.Bound := .any)
    (machineSets : MachineSets.Value := .none)
    (processingTimes : ParallelMachines.ProcessingTimes := .arbitrary)
    (release : ReleaseDates.Value := .none)
    (deadline : Deadlines.Value := .none)
    (precedence : Precedence.Value := .none)
    (communicationDelays : CommunicationDelays.Value := .none)
    (server : Servers.Value := .none)
    (forbiddenTimes : ForbiddenTimes.Value := .none)
    (encoding : ForbiddenTimes.Encoding := .standard)
    (objective : Objectives.Value) : Spec (family M) where
  module
    | .environment => environment
    | .machineCount => machineCount
    | .jobCount => jobCount
    | .processingTimes => processingTimes
    | .machineSets => machineSets
    | .releaseDates => release
    | .deadlines => deadline
    | .precedence => precedence
    | .communicationDelays => communicationDelays
    | .server => server
    | .forbiddenTimes => forbiddenTimes
    | .encoding => encoding
  objective := objective

/-- The non-preemptive problems. -/
abbrev nonpreemptive := family Nonpreemptive.model

end Lax434175.ParallelProblems
end

-- Lax888481.Scheduling
section
namespace Lax888481.Scheduling

/-- An instance of interval scheduling with eligible machine sets: `jobs` jobs on
`machines` machines, each job with a processing time, a deadline, a weight, and the set
of machines allowed to run it. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of machines. -/
  machines : ℕ
  /-- The processing time `p j` of job `j`. -/
  p : Fin jobs → ℕ
  /-- The deadline `d j` of job `j`. -/
  d : Fin jobs → ℕ
  /-- The weight `w j` of job `j`. -/
  w : Fin jobs → ℕ
  /-- The machines eligible to run job `j`. -/
  eligible : Fin jobs → Finset (Fin machines)
  /-- Every job takes at least one time unit. -/
  p_pos : ∀ j, 0 < p j
  /-- Every job fits before its deadline. -/
  p_le_d : ∀ j, p j ≤ d j

namespace Instance

variable (I : Instance)

variable {I}

variable (I)

end Instance

end Lax888481.Scheduling
end

-- Lax888481.InstanceEncoding
section
namespace Lax888481.InstanceEncoding

open Lax888481.Scheduling

/-- The number of jobs declared by a word: its first entry. -/
def jobCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of machines declared by a word: its second entry. -/
def machineCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The processing time of job `j`: the processing times follow the two header
entries. -/
def proc (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + j) 0

/-- The deadline of job `j`: the deadlines follow the processing times. -/
def due (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + jobCount x + j) 0

/-- The weight of job `j`: the weights follow the deadlines. -/
def wt (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + 2 * jobCount x + j) 0

/-- The `i`-th offset: the `n+1` offsets follow the weights. -/
def offset (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + 3 * jobCount x + i) 0

/-- The `t`-th entry of the target array, which follows the offsets. -/
def target (x : List ℕ) (t : ℕ) : ℕ := x.getD (3 + 4 * jobCount x + t) 0

/-- The word `x` encodes the instance `I`. -/
structure EncodesInstance (x : List ℕ) (I : Instance) : Prop where
  /-- The word declares `I`'s jobs. -/
  jobCount_eq : jobCount x = I.jobs
  /-- The word declares `I`'s machines. -/
  machineCount_eq : machineCount x = I.machines
  /-- The word consists of the two header entries, the three arrays of one number per
  job, the `n+1` offsets, and a target array as long as the last offset says. -/
  length_eq : x.length = 3 + 4 * I.jobs + offset x I.jobs
  /-- The processing times are `I`'s. -/
  proc_eq : ∀ j : Fin I.jobs, proc x j = I.p j
  /-- The deadlines are `I`'s. -/
  due_eq : ∀ j : Fin I.jobs, due x j = I.d j
  /-- The weights are `I`'s. -/
  wt_eq : ∀ j : Fin I.jobs, wt x j = I.w j
  /-- The block of the first job begins at the start of the target array. -/
  offset_zero : offset x 0 = 0
  /-- The offsets are nondecreasing, so they cut the target array into one block per
  job. -/
  offset_mono : ∀ j < I.jobs, offset x j ≤ offset x (j + 1)
  /-- Every entry of the target array is a machine. -/
  target_lt : ∀ t < offset x I.jobs, target x t < I.machines
  /-- The block of a job lists exactly its eligible machines. -/
  eligible_iff : ∀ (j : Fin I.jobs) (i : Fin I.machines),
    i ∈ I.eligible j ↔ ∃ t, offset x j ≤ t ∧ t < offset x (j + 1) ∧ target x t = i

/-- The word `x` presents the instance `I` together with the threshold `W`: an instance
block followed by the single entry `W`. -/
def EncodesDecisionInstance (x : List ℕ) (I : Instance) (W : ℕ) : Prop :=
  ∃ y, x = y ++ [W] ∧ EncodesInstance y I

end Lax888481.InstanceEncoding
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

-- Lax888481.SchedulingProblems
section
namespace Lax888481.SchedulingProblems
end Lax888481.SchedulingProblems
end

-- Lax888481.Theorem3
section
namespace Lax888481.Theorem3
end Lax888481.Theorem3
end

-- Lax434175.IsemLink
section
namespace Lax434175.IsemLink

open Lax434175 Lax434175.Problems Lax434175.Assembly

open Lax888481.Scheduling Lax888481.InstanceEncoding Lax888481.SchedulingProblems

open Lax888481.ParameterizedComplexity

/-- `P | M_j | Σ w_j Z_j` -/
def jitSets : Spec ParallelProblems.nonpreemptive :=
  ParallelProblems.spec _ .identical (machineSets := .sets) (objective := .sumWZ)

/-- The machine instance of an interval scheduling instance. -/
def base (I : Instance) : ParallelMachines.Inst where
  jobs := I.jobs
  machines := I.machines
  p := fun j _ => I.p j
  r := fun _ => 0

/-- The zoo instance of an interval scheduling instance. -/
def toZoo (I : Instance) : Inst ParallelProblems.nonpreemptive jitSets where
  base := base I
  data := fun i => by
    cases i
    · exact ()
    · exact ()
    · exact ()
    · exact ()
    · exact fun j i => i ∈ I.eligible j
    all_goals first | exact () | exact ((), ())
  admitted := fun i => by
    cases i
    · exact fun _ _ _ => rfl
    all_goals first | exact trivial | exact ⟨trivial, fun _ h => nomatch h⟩ | skip
    · exact fun _ => rfl
    all_goals first | exact trivial | exact ⟨fun _ _ h => h, trivial⟩
  objectiveData := (I.w, I.d)
  objectiveAdmitted := trivial

/-- The total weight of the jobs. -/
def totalWeight (I : Instance) : ℕ := ∑ j, I.w j

/-- Every job has an eligible machine. -/
def AllEligible (I : Instance) : Prop := ∀ j, (I.eligible j).Nonempty

/-- `P | M_j | Σ w_j Z_j` on the words of interval scheduling, for the
instances in which every job has an eligible machine, parameterized by the
number of machines. -/
def jitByMachines : Lax888481.ParameterizedComplexity.Problem where
  Domain := {x | ∃ I W, EncodesDecisionInstance x I W ∧ AllEligible I}
  Yes x := ∃ I W, EncodesDecisionInstance x I W ∧
    (problem _ jitSets).Decides (toZoo I) (((totalWeight I : ℤ) - W : ℤ) : ℚ)
  param x := machineCount x

end Lax434175.IsemLink
end
