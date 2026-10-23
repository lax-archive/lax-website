-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

-- Lax904597.Problems
section
namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

end DecisionProblem

end Lax904597.Problems
end

-- Lax799700.Problems
section
namespace Lax799700.Problems

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {L : Language.{0, 0}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end Lax799700.Problems
end

-- Lax904597.Interpretations
section
namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Interpretations.FOInterpretation
end Lax904597.Interpretations.FOInterpretation

namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction
end

-- Lax904597.Relativized
section
namespace Lax904597.Relativized
end Lax904597.Relativized

namespace Lax904597.Relativized.RelFOInterpretation
end Lax904597.Relativized.RelFOInterpretation

namespace Lax904597.Relativized.RelOrderedFOReduction
end Lax904597.Relativized.RelOrderedFOReduction
end

-- Lax904597.SecondOrder
section
namespace Lax904597.SecondOrder.SORealize
end Lax904597.SecondOrder.SORealize

namespace Lax904597.SecondOrder.soLang
end Lax904597.SecondOrder.soLang

namespace Lax904597.SecondOrder

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A second-order quantifier block: finitely many relation variables, with
given arities. The index type is arbitrary rather than an initial segment of
`ℕ`, so that constructions on blocks can build their natural index types. -/
structure SOBlock : Type 1 where
  /-- The index type of the relation variables of the block. -/
  ι : Type
  /-- A block has finitely many relation variables. -/
  [ιFinite : Finite ι]
  /-- The arity of each relation variable. -/
  arity : ι → ℕ

attribute [instance] SOBlock.ιFinite

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax904597.Sat
section
namespace Lax904597.Sat

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

/-- The relation symbols of CNF instances. -/
inductive satRel : ℕ → Type where
  /-- `isClause c`: the element `c` is a clause. -/
  | isClause : satRel 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : satRel 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : satRel 2
  deriving DecidableEq

/-- The relational language of CNF instances: a unary predicate singling out
clauses, and two binary predicates for positive and negative occurrences of a
variable in a clause. -/
def sat : Language :=
  ⟨fun _ => Empty, satRel⟩

end Lax904597.Sat
end

-- Lax799700.Common
section
namespace Lax799700.Common

open Lax904597.Sat

section Decode

variable {A : Type}

/-- The rank of a position: the number of positions strictly below it. This is
the place value's exponent. -/
noncomputable def bitRank (Le : A → A → Prop) (Posn : A → Prop) (p : A) : ℕ :=
  ({q | Posn q ∧ Le q p ∧ q ≠ p} : Set A).ncard

/-- The number encoded by the set `b` of positions: `∑ 2 ^ rank`. -/
noncomputable def binNum (Le : A → A → Prop) (Posn b : A → Prop) : ℕ :=
  ∑ᶠ p ∈ {p | Posn p ∧ b p}, 2 ^ bitRank Le Posn p

end Decode

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [sat.Structure A]

end SatOcc

end Lax799700.Common
end

-- Lax904597.Machines
section
namespace Lax904597.Machines.Config
end Lax904597.Machines.Config

namespace Lax904597.Machines.Config.ext
end Lax904597.Machines.Config.ext

namespace Lax904597.Machines.TMData.StepsIn
end Lax904597.Machines.TMData.StepsIn

namespace Lax904597.Machines

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Lax904597.Problems

variable {A : Type}

/-- A binary relation is a linear order: reflexive, transitive, antisymmetric
and total. -/
def IsLinOrd (Le : A → A → Prop) : Prop :=
  (∀ a, Le a a) ∧ (∀ a b c, Le a b → Le b c → Le a c) ∧
    (∀ a b, Le a b → Le b a → a = b) ∧ ∀ a b, Le a b ∨ Le b a

/-- A Turing machine presented as relations on a universe: the sorts, the
marks, the attributes of the transitions, the initial tape and the order along
which the head moves. -/
structure TMData (A : Type) where
  /-- Being a position – a tape cell, and equally a time step. -/
  Posn : A → Prop
  /-- The order on positions, along which the head moves. -/
  Le : A → A → Prop
  /-- Being a transition. -/
  Tr : A → Prop
  /-- Being a start state. -/
  Start : A → Prop
  /-- Being an accepting state. -/
  Acc : A → Prop
  /-- Being the blank symbol. -/
  Blank : A → Prop
  /-- This transition moves the head right (rather than left). -/
  Right : A → Prop
  /-- The state a transition applies in. -/
  Src : A → A → Prop
  /-- The symbol a transition reads. -/
  Read : A → A → Prop
  /-- The state a transition moves to. -/
  Dst : A → A → Prop
  /-- The symbol a transition writes. -/
  Write : A → A → Prop
  /-- The input: the symbol initially in a cell. -/
  Inp : A → A → Prop

namespace TMData

variable (M : TMData A)

end TMData

/-- Relation symbols of machine instances. -/
inductive turingRel : ℕ → Type
  /-- `posn p`: `p` is a position – a tape cell, and equally a time step. -/
  | posn : turingRel 1
  /-- `tr τ`: `τ` is a transition. -/
  | tr : turingRel 1
  /-- `start q`: `q` is a start state. -/
  | start : turingRel 1
  /-- `acc q`: `q` is an accepting state. -/
  | acc : turingRel 1
  /-- `blank a`: `a` is the blank symbol. -/
  | blank : turingRel 1
  /-- `right τ`: the transition `τ` moves the head right. -/
  | right : turingRel 1
  /-- `le p q`: the linear order along which the head moves. -/
  | le : turingRel 2
  /-- `tsrc τ q`: `τ` applies in the state `q`. -/
  | tsrc : turingRel 2
  /-- `tread τ a`: `τ` applies when reading the symbol `a`. -/
  | tread : turingRel 2
  /-- `tdst τ q`: `τ` moves to the state `q`. -/
  | tdst : turingRel 2
  /-- `twrite τ a`: `τ` writes the symbol `a`. -/
  | twrite : turingRel 2
  /-- `inp p a`: the cell `p` initially holds the symbol `a`. -/
  | inp : turingRel 2
  deriving DecidableEq

/-- The relational language of machine instances: positions with their order,
transitions with their attributes, the distinguished states and symbol, and the
initial tape. -/
def turing : Language :=
  ⟨fun _ => Empty, turingRel⟩

section Shorthands

variable [turing.Structure A]

end Shorthands

end Lax904597.Machines
end

-- Lax799700.JobSequencing
section
namespace Lax799700.JobSequencing

open Lax799700.Common Lax904597.Machines

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive jobSeqRel : ℕ → Type where
/-- `job j`: `j` is a job. -/
  | job : jobSeqRel 1
/-- `posn p`: `p` is a bit position. -/
  | posn : jobSeqRel 1
/-- `time j p`: the execution time of `j` has bit 1 at position `p`. -/
  | time : jobSeqRel 2
/-- `dline j p`: the deadline of `j` has bit 1 at position `p`. -/
  | dline : jobSeqRel 2
/-- `pen j p`: the penalty of `j` has bit 1 at position `p`. -/
  | pen : jobSeqRel 2
/-- `bnd p`: the penalty bound has bit 1 at position `p`. -/
  | bnd : jobSeqRel 1
/-- `le a b`: the linear order carrying the place values. -/
  | le : jobSeqRel 2
  deriving DecidableEq

/-- The relational language of job-sequencing instances: jobs and bit
positions, the bits of each job's execution time, deadline and penalty, the
bits of the penalty bound, and a linear order. -/
def jobSeq : FirstOrder.Language :=
  ⟨fun _ => Empty, jobSeqRel⟩

instance instIsRelationalJobSeq : FirstOrder.Language.IsRelational jobSeq := fun _ =>
  (inferInstance : IsEmpty Empty)

/-- `job j`: `j` is a job. -/
abbrev jsJob : jobSeq.Relations 1 :=
  .job

/-- `posn p`: `p` is a bit position. -/
abbrev jsPosn : jobSeq.Relations 1 :=
  .posn

/-- `time j p`: the execution time of `j` has bit 1 at position `p`. -/
abbrev jsTime : jobSeq.Relations 2 :=
  .time

/-- `dline j p`: the deadline of `j` has bit 1 at position `p`. -/
abbrev jsDline : jobSeq.Relations 2 :=
  .dline

/-- `pen j p`: the penalty of `j` has bit 1 at position `p`. -/
abbrev jsPen : jobSeq.Relations 2 :=
  .pen

/-- `bnd p`: the penalty bound has bit 1 at position `p`. -/
abbrev jsBnd : jobSeq.Relations 1 :=
  .bnd

/-- `le a b`: the linear order carrying the place values. -/
abbrev jsLe : jobSeq.Relations 2 :=
  .le

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [jobSeq.Structure A]

/-- `job j`: `j` is a job.  -/
def JSJob {A : Type} [jobSeq.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsJob ![a0]

/-- `posn p`: `p` is a bit position.  -/
def JSPosn {A : Type} [jobSeq.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsPosn ![a0]

/-- `time j p`: the execution time of `j` has bit 1 at position `p`.  -/
def JSTime {A : Type} [jobSeq.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsTime ![a0, a1]

/-- `dline j p`: the deadline of `j` has bit 1 at position `p`.  -/
def JSDline {A : Type} [jobSeq.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsDline ![a0, a1]

/-- `pen j p`: the penalty of `j` has bit 1 at position `p`.  -/
def JSPen {A : Type} [jobSeq.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsPen ![a0, a1]

/-- `bnd p`: the penalty bound has bit 1 at position `p`.  -/
def JSBnd {A : Type} [jobSeq.Structure A] (a0 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsBnd ![a0]

/-- `le a b`: the linear order carrying the place values.  -/
def JSLe {A : Type} [jobSeq.Structure A] (a0 : A) (a1 : A) : Prop :=
  FirstOrder.Language.Structure.RelMap jsLe ![a0, a1]

/-- The execution time of a job, decoded. -/
noncomputable def JSTimeVal (j : A) : ℕ := binNum JSLe JSPosn (JSTime j)

/-- The deadline of a job, decoded. -/
noncomputable def JSDlineVal (j : A) : ℕ := binNum JSLe JSPosn (JSDline j)

/-- The penalty of a job, decoded. -/
noncomputable def JSPenVal (j : A) : ℕ := binNum JSLe JSPosn (JSPen j)

end Shorthands

/-- The penalty bound of an instance, decoded. -/
noncomputable def JSBound (A : Type) [jobSeq.Structure A] : ℕ :=
  binNum (JSLe (A := A)) JSPosn JSBnd

section Schedule

variable {A : Type} [jobSeq.Structure A]

/-- The completion time of a job under a schedule: the total execution time of
the jobs scheduled at or before it. -/
noncomputable def JSCompletion (sched : A → A → Prop) (j : A) : ℕ :=
  ∑ᶠ i ∈ {i : A | JSJob i ∧ sched i j}, JSTimeVal i

/-- A job is late under a schedule when it completes after its deadline. -/
def JSLate (sched : A → A → Prop) (j : A) : Prop :=
  JSDlineVal j < JSCompletion sched j

/-- The total penalty of the jobs a schedule leaves late. -/
noncomputable def JSPenalty (sched : A → A → Prop) : ℕ :=
  ∑ᶠ j ∈ {j : A | JSJob j ∧ JSLate sched j}, JSPenVal j

end Schedule

section Problem

variable (A : Type) [jobSeq.Structure A]

/-- A job-sequencing instance is a yes-instance when its order is a linear
order and some schedule – some linear order on the universe – leaves late only
jobs whose penalties sum to at most the bound. -/
def HasGoodSchedule : Prop :=
  Finite A ∧ IsLinOrd (JSLe (A := A)) ∧
    ∃ sched : A → A → Prop, IsLinOrd sched ∧ JSPenalty sched ≤ JSBound A

end Problem

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

/-- The problem JobSequencing: does the structure satisfy `HasGoodSchedule`? -/
def JobSequencing : DecisionProblem Lax799700.JobSequencing.jobSeq :=
  DecisionProblem.ofPred HasGoodSchedule

end Lax799700.JobSequencing
end
