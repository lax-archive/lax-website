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

-- Lax434175.ParallelMachines
section
namespace Lax434175.ParallelMachines.Environment.holds
end Lax434175.ParallelMachines.Environment.holds

namespace Lax434175.ParallelMachines.ProcessingTimes.holds
end Lax434175.ParallelMachines.ProcessingTimes.holds

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

/-- The position of an environment in the chain identical, uniform, unrelated. -/
def Environment.rank : Environment → ℕ
  | .identical => 0
  | .uniform => 1
  | .unrelated => 2

inductive ProcessingTimes
  | unit
  | equal
  | oneOrTwo
  | arbitrary
  deriving DecidableEq

def ProcessingTimes.le : ProcessingTimes → ProcessingTimes → Bool
  | _, .arbitrary => true
  | .unit, _ => true
  | v, w => decide (v = w)

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
namespace Lax434175.Interruption.Mode.holds
end Lax434175.Interruption.Mode.holds

namespace Lax434175.Interruption

open Lax434175.Kernels Lax434175.Modules Lax434175.ParallelMachines Lax434175.Preemptive

inductive Mode
  | none
  | restarts
  | pmtn
  /-- Preemption without migration: all pieces of a job, or of an operation,
  occupy the same set of machines. -/
  | pmtnNoMigration
  deriving DecidableEq

end Lax434175.Interruption
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
namespace Lax434175.Assembly.Inst
end Lax434175.Assembly.Inst

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

end Lax434175.Assembly
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

-- Lax434175.Shops
section
namespace Lax434175.Shops.ProcessingTimes
end Lax434175.Shops.ProcessingTimes

namespace Lax434175.Shops.Sched
end Lax434175.Shops.Sched

namespace Lax434175.Shops.ShopType
end Lax434175.Shops.ShopType

namespace Lax434175.Shops.NoWait.constraint
end Lax434175.Shops.NoWait.constraint

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

inductive NoWait
  | none
  | noWait
  deriving DecidableEq

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

/-- The release date of the setup of an item: the release date of its job if
the item starts when its job starts (the first operation of the job), and `0`
otherwise. -/
def setupRelease {Item : Type} (start jobStart release : Item → ℚ) (a : Item) : ℚ :=
  if start a = jobStart a then release a else 0

end Lax434175.Servers
end

-- Lax434175.ShopExtras
section
namespace Lax434175.ShopExtras

open Lax434175.Kernels Lax434175.Modules Lax434175.Shops

inductive NoIdle
  | none
  | noIdle
  deriving DecidableEq

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

end Lax434175.ShopExtras
end

-- Lax434175.Transportation
section
namespace Lax434175.Transportation

open Lax434175.Kernels Lax434175.Modules Lax434175.Shops

/-- The delays of an instance. -/
abbrev Delays (x : Inst) := (j : Fin x.jobs) → Fin (x.ops j) → Fin (x.ops j) → ℕ

inductive Shape
  | none
  | uniform
  | twoValues
  | job
  | source
  | jobSource
  | pairSymmetric
  | pair
  | jobPairSymmetric
  | jobPair
  deriving DecidableEq

/-- The delays of a shape. -/
def Shape.holds {x : Inst} : Shape → Delays x → Prop
  | .none, t => ∀ j k l, t j k l = 0
  | .uniform, t => ∃ T, ∀ j k l, t j k l = T
  | .twoValues, t => ∃ T₁ T₂, ∀ j, (∀ k l, t j k l = T₁) ∨ (∀ k l, t j k l = T₂)
  | .job, t => ∀ j k l k' l', t j k l = t j k' l'
  | .source, t => ∃ g : ℕ → ℕ, ∀ j k l, t j k l = g k.val
  | .jobSource, t => ∀ j k l l', t j k l = t j k l'
  | .pairSymmetric, t => ∃ g : ℕ → ℕ → ℕ, (∀ a b, g a b = g b a) ∧ ∀ j k l, t j k l = g k.val l.val
  | .pair, t => ∃ g : ℕ → ℕ → ℕ, ∀ j k l, t j k l = g k.val l.val
  | .jobPairSymmetric, t => ∀ j k l, t j k l = t j l k
  | .jobPair, _ => True

def Shape.le : Shape → Shape → Bool
  | _, .jobPair => true
  | .none, _ => true
  | .uniform, .none => false
  | .uniform, _ => true
  | .twoValues, .twoValues | .twoValues, .job | .twoValues, .jobSource
  | .twoValues, .jobPairSymmetric => true
  | .job, .job | .job, .jobSource | .job, .jobPairSymmetric => true
  | .source, .source | .source, .jobSource | .source, .pair => true
  | .jobSource, .jobSource => true
  | .pairSymmetric, .pairSymmetric | .pairSymmetric, .pair
  | .pairSymmetric, .jobPairSymmetric => true
  | .pair, .pair => true
  | .jobPairSymmetric, .jobPairSymmetric => true
  | _, _ => false

/-- The empty moving times of the robot, from a machine to a machine. -/
abbrev EmptyMoves (x : Inst) := Fin x.machines → Fin x.machines → ℕ

/-- The time the robot needs to travel empty from a set of machines to
another: the largest empty moving time from a machine of the first to a
machine of the second. -/
def emptyTime {m : ℕ} (e : Fin m → Fin m → ℕ) (S S' : Finset (Fin m)) : ℕ :=
  S.sup fun i => S'.sup (e i)

/-- A value of the field: a shape of delays, whether a robot carries the
jobs, and whether the robot needs time to travel empty. -/
structure Value where
  shape : Shape
  robot : Bool := false
  emptyMoves : Bool := false

/-- No transportation delays and no robot. -/
def Value.none : Value := ⟨.none, false, false⟩

/-- The data of the field: the delays and the empty moving times. -/
abbrev Data (x : Inst) := Delays x × EmptyMoves x

/-- The delays have the shape, and unless the value has a robot with empty
moves, the empty moving times are `0`. -/
def Value.admits {x : Inst} (v : Value) (d : Data x) : Prop :=
  v.shape.holds d.1 ∧ ((v.robot && v.emptyMoves) = false → ∀ i i', d.2 i i' = 0)

/-- The shape is a special case, both values have a robot or neither has,
and empty moves only if the other value has them. -/
def Value.le (v w : Value) : Bool :=
  Shape.le v.shape w.shape && decide (v.robot = w.robot) && (!v.emptyMoves || w.emptyMoves)

end Lax434175.Transportation
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

/-- The time an operation needs when it occupies a set of machines. -/
def duration (x : Inst) (o : Op x) (S : Finset (Fin x.machines)) : ℕ :=
  S.sup (x.p o.1 o.2)

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

/-- The pieces of an operation. -/
def piecesOf {x : Inst} (σ : Sched x) (o : Op x) : List (Piece x) :=
  σ.pieces.filter (fun q => decide (q.op = o))

/-- The pieces of a job. -/
def piecesOfJob {x : Inst} (σ : Sched x) (j : Fin x.jobs) : List (Piece x) :=
  σ.pieces.filter (fun q => decide (q.op.1 = j))

/-- Two pieces do not overlap in time. -/
def Apart {x : Inst} (a b : Piece x) : Prop :=
  a.finish ≤ b.start ∨ b.finish ≤ a.start

/-- The start of the first piece of an operation. -/
def opStart {x : Inst} (σ : Sched x) (o : Op x) : NNRat :=
  (((piecesOf σ o).map Piece.start).min?).getD 0

/-- The end of the last piece of an operation. -/
def opFinish {x : Inst} (σ : Sched x) (o : Op x) : NNRat :=
  (((piecesOf σ o).map Piece.finish).max?).getD 0

/-- The fraction of an operation that a schedule completes. -/
def fraction (x : Inst) (σ : Sched x) (o : Op x) : NNRat :=
  ((piecesOf σ o).map (fun q => q.length / (duration x o q.machines : NNRat))).sum

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

/-- The number of machines, a parameter of the kernel. -/
def machines : kernel.Inst → ℕ := Inst.machines

/-- A piece processes its operation entirely. -/
def Complete {x : Inst} (q : Piece x) : Prop :=
  q.length = (duration x q.op q.machines : NNRat)

/-- The schedules that respect a way of interruption. -/
def holds : Interruption.Mode → (x : Inst) → Sched x → Prop
  | .none, x, σ => ∀ o : Op x, ∃ q, piecesOf σ o = [q] ∧
      q.length = (duration x o q.machines : NNRat) ∧ ∃ n : ℕ, q.start = (n : NNRat)
  | .restarts, _, σ => ∀ o, ∃ q ∈ piecesOf σ o, Complete q ∧
      ∀ q' ∈ piecesOf σ o, q'.finish ≤ q.finish ∧ (Complete q' → q'.finish = q.finish)
  | .pmtn, x, σ => ∀ o, fraction x σ o = 1 ∨ ∃ q ∈ piecesOf σ o, duration x o q.machines = 0
  | .pmtnNoMigration, x, σ => ∀ o,
      (fraction x σ o = 1 ∨ ∃ q ∈ piecesOf σ o, duration x o q.machines = 0) ∧
        ∀ q ∈ piecesOf σ o, ∀ q' ∈ piecesOf σ o, q.machines = q'.machines

/-- The interruption field. -/
def interruption : Module kernel where
  Value := Interruption.Mode
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := holds v x σ
  le v w := decide (v = w)
  embed _ _ _ := ()

inductive Structure
  | single
  | open
  | flow
  | job
  | flexibleFlow
  deriving DecidableEq

/-- The instances of a job structure. -/
def Structure.holds : Structure → Inst → Prop
  | .single, x => ∀ j, x.ops j = 1
  | .open, x => ∀ j, x.ops j = x.machines
  | .flow, x => ∀ j, x.ops j = x.machines
  | .job, _ => True
  | .flexibleFlow, x => ∀ j, x.ops j = 2

/-- The operations of every job are processed in their given order. -/
def InOrder (x : Inst) (σ : Sched x) : Prop :=
  ∀ j (k k' : Fin (x.ops j)), k < k' → opFinish σ ⟨j, k⟩ ≤ opStart σ ⟨j, k'⟩

/-- The order a job structure imposes on the operations of a job. -/
def Structure.ordered : Structure → (x : Inst) → Sched x → Prop
  | .single, _, _ => True
  | .open, _, _ => True
  | .flow, x, σ => InOrder x σ
  | .job, x, σ => InOrder x σ
  | .flexibleFlow, x, σ => InOrder x σ

def Structure.le : Structure → Structure → Bool
  | .single, .job | .flow, .job | .flexibleFlow, .job => true
  | v, w => decide (v = w)

/-- The job-structure field. -/
def jobStructure : Module kernel where
  Value := Structure
  Data _ _ := Unit
  admits v x _ := v.holds x
  constraint v x _ σ := v.ordered x σ
  le := Structure.le
  embed _ _ _ := ()

/-- The instances of a machine environment. -/
def environmentHolds : ParallelMachines.Environment → Inst → Prop
  | .identical, x => ∀ (o : Op x) i i', x.p o.1 o.2 i = x.p o.1 o.2 i'
  | .uniform, x => ∃ (q : Op x → ℕ) (s : Fin x.machines → ℕ),
      ∀ (o : Op x) i, 0 < s i ∧ x.p o.1 o.2 i * s i = q o
  | .unrelated, _ => True

/-- The machine-environment field. -/
def environment : Module kernel :=
  Module.ofRestriction ParallelMachines.Environment (fun v x => environmentHolds v x)
    (fun v w => decide (v.rank ≤ w.rank))

/-- The instances of a processing-time restriction. -/
def processingTimesHolds : ParallelMachines.ProcessingTimes → Inst → Prop
  | .unit, x => ∀ (o : Op x) i, x.p o.1 o.2 i = 1
  | .equal, x => ∃ p, ∀ (o : Op x) i, x.p o.1 o.2 i = p
  | .oneOrTwo, x => ∀ (o : Op x) i, x.p o.1 o.2 i = 1 ∨ x.p o.1 o.2 i = 2
  | .arbitrary, _ => True

/-- The processing-time field. -/
def processingTimes : Module kernel :=
  Module.ofRestriction ParallelMachines.ProcessingTimes (fun v x => processingTimesHolds v x)
    ParallelMachines.ProcessingTimes.le

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

/-- Scheduling with operations as a machine model on parallel machines: a job
occupies a set of machines if one of its pieces does. -/
def model : ParallelMachines.Model where
  kernel := kernel
  inst x := x.toPar
  jobs_eq _ := rfl
  uses _ σ j S := ∃ q ∈ piecesOfJob σ j, q.machines = S

/-- A piece of one operation and a piece of another share a machine. -/
def Shares {x : Inst} (σ : Sched x) (a b : Op x) : Prop :=
  ∃ qa ∈ piecesOf σ a, ∃ qb ∈ piecesOf σ b, ¬ Disjoint qa.machines qb.machines

/-- The server field: every operation needs a setup. -/
def server : Module kernel where
  Value := Servers.Value
  Data v x := Servers.Data (Op x) v
  admits v _ d := Servers.Admits v d
  constraint v x d σ := ∀ s, Servers.view v d = some s →
    Servers.Served (fun o : Op x => (opStart σ o : ℚ)) (fun o => (opFinish σ o : ℚ))
      (Servers.setupRelease (fun o : Op x => (opStart σ o : ℚ))
        (fun o => (kernel.start x σ o.1 : ℚ)) (fun o => (x.r o.1 : ℚ)))
      (Shares σ) s
  le := Servers.le
  embed h _ d := Servers.embed h d

/-- The time an operation needs on the first machine; for shops, where the
time does not depend on the machine, its processing time. Without machines no
operation can be processed, and the time is taken to be `1`. -/
def opTime (x : Inst) (o : Op x) : ℕ :=
  if h : 0 < x.machines then x.p o.1 o.2 ⟨0, h⟩ else 1

/-- The no-wait field. -/
def noWait : Module kernel where
  Value := Shops.NoWait
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := v = .noWait →
    ∀ j, kernel.completion x σ j = kernel.start x σ j + ∑ k, (opTime x ⟨j, k⟩ : NNRat)
  le v w := decide (v = w)
  embed _ _ _ := ()

/-- Of two operations of a job, the later one waits for the delay, unless both
delays between them are `0`. -/
def Delayed (x : Inst) (t : Transportation.Delays x.toShop) (σ : Sched x) : Prop :=
  ∀ j (k l : Fin (x.ops j)), k ≠ l → (t j k l = 0 ∧ t j l k = 0) ∨
    opFinish σ ⟨j, k⟩ + (t j k l : NNRat) ≤ opStart σ ⟨j, l⟩ ∨
    opFinish σ ⟨j, l⟩ + (t j l k : NNRat) ≤ opStart σ ⟨j, k⟩

/-- The machines that the pieces of an operation occupy. -/
def opMachines {x : Inst} (σ : Sched x) (o : Op x) : Finset (Fin x.machines) :=
  ((piecesOf σ o).map Piece.machines).foldr (· ∪ ·) ∅

/-- A single robot carries every job from each operation to the next, and
between two transports it travels empty from the machines where it delivers
the one to the machines where it picks up the other. -/
def Carried (x : Inst) (t : Transportation.Delays x.toShop)
    (e : Transportation.EmptyMoves x.toShop) (σ : Sched x) : Prop :=
  ∃ depart : (j : Fin x.jobs) → Fin (x.ops j) → ℕ,
    (∀ j (k l : Fin (x.ops j)), l.val = k.val + 1 →
      opFinish σ ⟨j, k⟩ ≤ (depart j k : NNRat) ∧
        ((depart j k + t j k l : ℕ) : NNRat) ≤ opStart σ ⟨j, l⟩) ∧
    ∀ j (k l : Fin (x.ops j)) j' (k' l' : Fin (x.ops j')), l.val = k.val + 1 →
      l'.val = k'.val + 1 → (⟨j, k⟩ : Op x) ≠ ⟨j', k'⟩ →
      depart j k + t j k l +
          Transportation.emptyTime e (opMachines σ ⟨j, l⟩) (opMachines σ ⟨j', k'⟩) ≤
        depart j' k' ∨
      depart j' k' + t j' k' l' +
          Transportation.emptyTime e (opMachines σ ⟨j', l'⟩) (opMachines σ ⟨j, k⟩) ≤
        depart j k

/-- The field of transportation delays. -/
def transportation : Module kernel where
  Value := Transportation.Value
  Data _ x := Transportation.Data x.toShop
  admits v _ d := v.admits d
  constraint v x d σ := Delayed x d.1 σ ∧ (v.robot = true → Carried x d.1 d.2 σ)
  le := Transportation.Value.le
  embed _ _ d := d

/-- A piece of an operation occupies a machine. -/
def Occupies {x : Inst} (σ : Sched x) (o : Op x) (i : Fin x.machines) : Prop :=
  ∃ q ∈ piecesOf σ o, i ∈ q.machines

/-- Every operation on a machine is immediately followed by another one on
that machine, unless none completes later. -/
def Contiguous (x : Inst) (σ : Sched x) : Prop :=
  ∀ i (a : Op x), Occupies σ a i →
    (∃ b : Op x, b ≠ a ∧ Occupies σ b i ∧ opStart σ b = opFinish σ a) ∨
    ∀ b : Op x, Occupies σ b i → opFinish σ b ≤ opFinish σ a

/-- The no-idle field. -/
def noIdle : Module kernel where
  Value := ShopExtras.NoIdle
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := v = .noIdle → Contiguous x σ
  le v w := decide (v = w)
  embed _ _ _ := ()

/-- On some machine, operation `b` follows operation `a`: `b` starts after `a`
completes, and no other operation on that machine lies in between. -/
def Follows {x : Inst} (σ : Sched x) (a b : Op x) : Prop :=
  opFinish σ a ≤ opStart σ b ∧ ∃ i, Occupies σ a i ∧ Occupies σ b i ∧
    ∀ c : Op x, c ≠ a → c ≠ b → Occupies σ c i →
      ¬ (opFinish σ a ≤ opStart σ c ∧ opFinish σ c ≤ opStart σ b)

/-- The batch-setup field. -/
def batchSetups : Module kernel where
  Value := ShopExtras.BatchSetups
  Data v x := ShopExtras.BatchSetups.Data v x.toShop
  admits _ _ _ := True
  constraint v x d σ := ∀ a b : Op x,
    v.batch (x := x.toShop) d a.1 ≠ v.batch (x := x.toShop) d b.1 →
    (Shares σ a b → opFinish σ a ≤ opStart σ b ∨ opFinish σ b ≤ opStart σ a) ∧
    (Follows σ a b → opFinish σ a + (v.setup (x := x.toShop) d (v.batch (x := x.toShop) d a.1)
        (v.batch (x := x.toShop) d b.1) : NNRat) ≤ opStart σ b)
  le := ShopExtras.BatchSetups.le
  embed h x d := ShopExtras.BatchSetups.embed h x.toShop d

end Lax434175.Operations
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
namespace Lax434175.OperationsFamily.ofShopTimes
end Lax434175.OperationsFamily.ofShopTimes

namespace Lax434175.OperationsFamily.ofShopType
end Lax434175.OperationsFamily.ofShopType

namespace Lax434175.OperationsFamily

open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly

open Lax434175 Lax434175.Operations

/-- The fields of the family. -/
inductive FieldName
  | interruption
  | jobStructure
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
  | noWait
  | transportation
  | noIdle
  | batchSetups
  deriving DecidableEq

/-- The problems on parallel machines and in shops. -/
abbrev family : Family Operations.kernel :=
  Thresholds.family FieldName fun
    | .interruption => Operations.interruption
    | .jobStructure => Operations.jobStructure
    | .environment => Operations.environment
    | .machineCount => Counts.module _ Operations.machines 1
    | .jobCount => Counts.module _ Operations.kernel.jobs
    | .processingTimes => Operations.processingTimes
    | .machineSets => Operations.machineSets
    | .releaseDates => ReleaseDates.module _
    | .deadlines => Deadlines.module _
    | .precedence => Precedence.module _ Operations.machines
    | .communicationDelays => CommunicationDelays.module Operations.model
    | .server => Operations.server
    | .forbiddenTimes => ForbiddenTimes.module _
    | .encoding => ForbiddenTimes.encoding _
    | .noWait => Operations.noWait
    | .transportation => Operations.transportation
    | .noIdle => Operations.noIdle
    | .batchSetups => Operations.batchSetups

/-- The specification `α | β | γ`. -/
def spec (interruption : Interruption.Mode := .none)
    (shopType : Structure := .single)
    (environment : ParallelMachines.Environment := .identical)
    (machineCount : Counts.Bound := .any)
    (jobCount : Counts.Bound := .any)
    (processingTimes : ParallelMachines.ProcessingTimes := .arbitrary)
    (machineSets : Machines := .par .none)
    (release : ReleaseDates.Value := .none)
    (deadline : Deadlines.Value := .none)
    (precedence : Precedence.Value := .none)
    (communicationDelays : CommunicationDelays.Value := .none)
    (server : Servers.Value := .none)
    (forbiddenTimes : ForbiddenTimes.Value := .none)
    (encoding : ForbiddenTimes.Encoding := .standard)
    (waiting : Shops.NoWait := .none)
    (transportation : Transportation.Value := .none)
    (idling : ShopExtras.NoIdle := .none)
    (setups : ShopExtras.BatchSetups := .none)
    (objective : Objectives.Value) : Spec family where
  module
    | .interruption => interruption
    | .jobStructure => shopType
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
    | .noWait => waiting
    | .transportation => transportation
    | .noIdle => idling
    | .batchSetups => setups
  objective := objective

end Lax434175.OperationsFamily
end

-- Lax434175.ZooShops
section
namespace Lax434175.ZooShops

open Lax434175 Lax434175.Problems Lax434175.Assembly

/-- The family of the problems listed here. -/
abbrev F := OperationsFamily.family

/-- `F2;R1|pij=p;tk;rj|ΣTj` -/
def p159 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .source, robot := true })
    (machineCount := .atMost 2) (objective := .sumT)

end Lax434175.ZooShops
end
