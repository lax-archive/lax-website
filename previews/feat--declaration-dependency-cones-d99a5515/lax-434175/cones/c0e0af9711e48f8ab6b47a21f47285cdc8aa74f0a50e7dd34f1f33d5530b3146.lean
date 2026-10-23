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

-- Lax434175.Nonpreemptive
section
namespace Lax434175.Nonpreemptive
end Lax434175.Nonpreemptive

namespace Lax434175.Nonpreemptive.Sched
end Lax434175.Nonpreemptive.Sched
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

/-- The number of machines, a parameter of the kernel. -/
def machines : kernel.Inst → ℕ := Inst.machines

/-- Every job has exactly one operation per machine. -/
def OnePerMachine (x : Inst) : Prop :=
  ∀ j, x.ops j = x.machines

/-- The operations of every job are processed in their given order. -/
def InOrder (x : Inst) (σ : Sched x) : Prop :=
  ∀ j (k k' : Fin (x.ops j)), k < k' → finish x σ ⟨j, k⟩ ≤ σ.start j k'

inductive ShopType
  | open
  | flow
  | job
  | flexibleFlow
  deriving DecidableEq

/-- The instances of a shop type. -/
def ShopType.holds : ShopType → Inst → Prop
  | .open, x => OnePerMachine x
  | .flow, x => OnePerMachine x
  | .job, _ => True
  | .flexibleFlow, x => ∀ j, x.ops j = 2

/-- The order a shop type imposes on the operations of a job. -/
def ShopType.ordered : ShopType → (x : Inst) → Sched x → Prop
  | .open, _, _ => True
  | .flow, x, σ => InOrder x σ
  | .job, x, σ => InOrder x σ
  | .flexibleFlow, x, σ => InOrder x σ

def ShopType.le : ShopType → ShopType → Bool
  | .flow, .job | .flexibleFlow, .job => true
  | v, w => decide (v = w)

/-- The shop-type field. -/
def shopType : Module kernel where
  Value := ShopType
  Data _ _ := Unit
  admits v x _ := v.holds x
  constraint v x _ σ := v.ordered x σ
  le := ShopType.le
  embed _ _ _ := ()

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

/-- The machine field. -/
def machineSets : Module kernel where
  Value := Machines
  Data := Machines.Data
  admits v _ d := v.admits d
  constraint v _ d σ := ∀ j k, v.view d j k (Sched.machines σ j k)
  le := Machines.le
  embed := Machines.embed

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

inductive NoWait
  | none
  | noWait
  deriving DecidableEq

/-- Every job is processed without interruption. -/
def NoWait.constraint : NoWait → (x : Inst) → Sched x → Prop
  | .none, _, _ => True
  | .noWait, x, σ => ∀ j, jobCompletion x σ j = jobStart x σ j + ∑ k, x.p j k

/-- The no-wait field. -/
def noWait : Module kernel where
  Value := NoWait
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := v.constraint x σ
  le v w := decide (v = w)
  embed _ _ _ := ()

end Lax434175.Shops
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

/-- The server field of shops: every operation needs a setup. -/
def shop : Module Shops.kernel where
  Value := Value
  Data v x := Data (Shops.Op x) v
  admits v _ d := Admits v d
  constraint v x d σ := ∀ s, view v d = some s →
    Served (fun o : Shops.Op x => (Shops.Sched.start σ o.1 o.2 : ℚ))
      (fun o => (Shops.finish x σ o : ℚ))
      (setupRelease (fun o : Shops.Op x => (Shops.Sched.start σ o.1 o.2 : ℚ))
        (fun o => (Shops.jobStart x σ o.1 : ℚ)) (fun o => (x.r o.1 : ℚ)))
      (fun a b => ¬ Disjoint (Shops.Sched.machines σ a.1 a.2) (Shops.Sched.machines σ b.1 b.2)) s
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
namespace Lax434175.Parameters.FieldParameter
end Lax434175.Parameters.FieldParameter

namespace Lax434175.Parameters.InPlace
end Lax434175.Parameters.InPlace

namespace Lax434175.Parameters

open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly

/-- `A` reduces to `B` by a reduction that relates the parameter values of
an instance and of its image by `R`. -/
def ReducibleWith {A B : Problem} {α β : Type} (κA : A.Inst → α) (κB : B.Inst → β)
    (R : α → β → Prop) : Prop :=
  ∃ r : DecisionReduction A B, r.Sound ∧ ∀ x D, R (κA x) (κB (r.map x D))

end Lax434175.Parameters
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

-- Lax434175.ShopExtras
section
namespace Lax434175.ShopExtras

open Lax434175.Kernels Lax434175.Modules Lax434175.Shops

inductive NoIdle
  | none
  | noIdle
  deriving DecidableEq

/-- An operation occupies a machine. -/
def Occupies {x : Inst} (σ : Sched x) (o : Op x) (i : Fin x.machines) : Prop :=
  i ∈ σ.machines o.1 o.2

/-- Every operation on a machine is immediately followed by another one on
that machine, unless none completes later. -/
def Contiguous (x : Inst) (σ : Sched x) : Prop :=
  ∀ i (a : Op x), Occupies σ a i →
    (∃ b : Op x, b ≠ a ∧ Occupies σ b i ∧ σ.start b.1 b.2 = finish x σ a) ∨
    ∀ b : Op x, Occupies σ b i → finish x σ b ≤ finish x σ a

/-- The no-idle field. -/
def noIdle : Module kernel where
  Value := NoIdle
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := v = .noIdle → Contiguous x σ
  le v w := decide (v = w)
  embed _ _ _ := ()

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

/-- Of two operations of a job, the later one waits for the delay. -/
def Delayed (x : Inst) (t : Delays x) (σ : Sched x) : Prop :=
  ∀ j (k l : Fin (x.ops j)), k ≠ l →
    finish x σ ⟨j, k⟩ + t j k l ≤ σ.start j l ∨ finish x σ ⟨j, l⟩ + t j l k ≤ σ.start j k

/-- The empty moving times of the robot, from a machine to a machine. -/
abbrev EmptyMoves (x : Inst) := Fin x.machines → Fin x.machines → ℕ

/-- The time the robot needs to travel empty from a set of machines to
another: the largest empty moving time from a machine of the first to a
machine of the second. -/
def emptyTime {m : ℕ} (e : Fin m → Fin m → ℕ) (S S' : Finset (Fin m)) : ℕ :=
  S.sup fun i => S'.sup (e i)

/-- A single robot carries every job from each operation to the next, and
between two transports it travels empty from the machines where it delivers
the one to the machines where it picks up the other. -/
def Carried (x : Inst) (t : Delays x) (e : EmptyMoves x) (σ : Sched x) : Prop :=
  ∃ depart : (j : Fin x.jobs) → Fin (x.ops j) → ℕ,
    (∀ j (k l : Fin (x.ops j)), l.val = k.val + 1 →
      finish x σ ⟨j, k⟩ ≤ depart j k ∧ depart j k + t j k l ≤ σ.start j l) ∧
    ∀ j (k l : Fin (x.ops j)) j' (k' l' : Fin (x.ops j')), l.val = k.val + 1 →
      l'.val = k'.val + 1 → (⟨j, k⟩ : Op x) ≠ ⟨j', k'⟩ →
      depart j k + t j k l + emptyTime e (σ.machines j l) (σ.machines j' k') ≤ depart j' k' ∨
      depart j' k' + t j' k' l' + emptyTime e (σ.machines j' l') (σ.machines j k) ≤ depart j k

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

/-- The field of transportation delays. -/
def module : Module kernel where
  Value := Value
  Data _ x := Data x
  admits v _ d := v.admits d
  constraint v x d σ := Delayed x d.1 σ ∧ (v.robot = true → Carried x d.1 d.2 σ)
  le := Value.le
  embed _ _ d := d

end Lax434175.Transportation
end

-- Lax434175.ShopProblems
section
namespace Lax434175.ShopProblems

open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly

open Lax434175

/-- The constraint fields of the family. -/
inductive FieldName
  | shopType
  | machineSets
  | machineCount
  | jobCount
  | processingTimes
  | noWait
  | transportation
  | server
  | noIdle
  | batchSetups
  | releaseDates
  | deadlines
  | precedence
  deriving DecidableEq

/-- The shop problems. -/
abbrev family : Family Shops.kernel :=
  Thresholds.family FieldName fun
    | .shopType => Shops.shopType
    | .machineSets => Shops.machineSets
    | .machineCount => Counts.module _ Shops.machines 1
    | .jobCount => Counts.module _ Shops.kernel.jobs
    | .processingTimes => Shops.processingTimes
    | .noWait => Shops.noWait
    | .transportation => Transportation.module
    | .server => Servers.shop
    | .noIdle => ShopExtras.noIdle
    | .batchSetups => ShopExtras.batchSetups
    | .releaseDates => ReleaseDates.module _
    | .deadlines => Deadlines.module _
    | .precedence => Precedence.module _ Shops.machines

/-- The specification `α | β | γ` of a shop problem. -/
def spec (shopType : Shops.ShopType)
    (machineSets : Shops.Machines)
    (machineCount : Counts.Bound := .any)
    (jobCount : Counts.Bound := .any)
    (processingTimes : Shops.ProcessingTimes := .arbitrary)
    (waiting : Shops.NoWait := .none)
    (transportation : Transportation.Value := .none)
    (server : Servers.Value := .none)
    (idling : ShopExtras.NoIdle := .none)
    (setups : ShopExtras.BatchSetups := .none)
    (release : ReleaseDates.Value := .none)
    (deadline : Deadlines.Value := .none)
    (precedence : Precedence.Value := .none)
    (objective : Objectives.Value) : Spec family where
  module
    | .shopType => shopType
    | .machineSets => machineSets
    | .machineCount => machineCount
    | .jobCount => jobCount
    | .processingTimes => processingTimes
    | .noWait => waiting
    | .transportation => transportation
    | .server => server
    | .noIdle => idling
    | .batchSetups => setups
    | .releaseDates => release
    | .deadlines => deadline
    | .precedence => precedence
  objective := objective

end Lax434175.ShopProblems
end

-- Lax434175.Encodings
section
namespace Lax434175.Encodings

open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Parameters

/-- `F2 || γ` -/
def flow2 (objective : Objectives.Value) : Spec ShopProblems.family :=
  ShopProblems.spec (shopType := .flow) (machineSets := .byPosition) (machineCount := .atMost 2)
    (objective := objective)

/-- `FF(1,m) || γ` -/
def flexibleFlow (objective : Objectives.Value) : Spec ShopProblems.family :=
  ShopProblems.spec (shopType := .flexibleFlow) (machineSets := .stages) (objective := objective)

/-- The numbers of jobs and machines of a shop instance. -/
def shopSize {s : Spec ShopProblems.family} (x : Inst ShopProblems.family s) : ℕ × ℕ :=
  (x.base.jobs, x.base.machines)

axiom flow2_flexibleFlow :
    ReducibleWith (A := problem _ (flow2 .sumZ)) (B := problem _ (flexibleFlow .sumZ)) shopSize shopSize
      (fun a b => b.1 = a.1 ∧ b.2 = 2)

end Lax434175.Encodings
end
