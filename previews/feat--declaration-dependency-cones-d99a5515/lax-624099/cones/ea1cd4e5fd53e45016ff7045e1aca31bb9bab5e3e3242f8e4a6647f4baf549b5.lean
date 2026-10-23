-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Relation
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
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

-- Lax624099.ValueInvention
section
namespace Lax624099
end Lax624099

namespace Lax624099.ValueInvention
end Lax624099.ValueInvention

namespace Lax624099.ValueInvention.IsOld
end Lax624099.ValueInvention.IsOld

namespace Lax624099.ValueInvention.oldMarkStructure
end Lax624099.ValueInvention.oldMarkStructure

namespace Lax624099.ValueInvention.oldRel
end Lax624099.ValueInvention.oldRel

namespace Lax624099.ValueInvention.oldRel.old
end Lax624099.ValueInvention.oldRel.old
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

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax624099.ClassRE
section
namespace Lax624099.ClassRE
end Lax624099.ClassRE

namespace Lax624099.ClassRE.DecisionProblem
end Lax624099.ClassRE.DecisionProblem
end

-- Lax624099.Problems
section
namespace Lax624099
end Lax624099

namespace Lax624099.Problems
end Lax624099.Problems

namespace Lax624099.Problems.DecisionProblem
end Lax624099.Problems.DecisionProblem

namespace Lax624099.Problems.DecisionProblem.ofPred
end Lax624099.Problems.DecisionProblem.ofPred
end

-- Lax624099.CodeHalting
section
namespace Lax624099.CodeHalting
end Lax624099.CodeHalting

namespace Lax624099.CodeHalting.DecodesTo
end Lax624099.CodeHalting.DecodesTo

namespace Lax624099.CodeHalting.codeRel
end Lax624099.CodeHalting.codeRel

namespace Lax624099.CodeHalting.codeRel.carg1
end Lax624099.CodeHalting.codeRel.carg1

namespace Lax624099.CodeHalting.codeRel.carg2
end Lax624099.CodeHalting.codeRel.carg2

namespace Lax624099.CodeHalting.codeRel.ccomp
end Lax624099.CodeHalting.codeRel.ccomp

namespace Lax624099.CodeHalting.codeRel.cleft
end Lax624099.CodeHalting.codeRel.cleft

namespace Lax624099.CodeHalting.codeRel.cpair
end Lax624099.CodeHalting.codeRel.cpair

namespace Lax624099.CodeHalting.codeRel.cprec
end Lax624099.CodeHalting.codeRel.cprec

namespace Lax624099.CodeHalting.codeRel.crfind
end Lax624099.CodeHalting.codeRel.crfind

namespace Lax624099.CodeHalting.codeRel.cright
end Lax624099.CodeHalting.codeRel.cright

namespace Lax624099.CodeHalting.codeRel.croot
end Lax624099.CodeHalting.codeRel.croot

namespace Lax624099.CodeHalting.codeRel.csucc
end Lax624099.CodeHalting.codeRel.csucc

namespace Lax624099.CodeHalting.codeRel.czero
end Lax624099.CodeHalting.codeRel.czero
end

-- Lax624099.FiniteSatisfiability
section
namespace Lax624099.FiniteSatisfiability
end Lax624099.FiniteSatisfiability

namespace Lax624099.FiniteSatisfiability.FinSat
end Lax624099.FiniteSatisfiability.FinSat

namespace Lax624099.FiniteSatisfiability.finsatRel
end Lax624099.FiniteSatisfiability.finsatRel

namespace Lax624099.FiniteSatisfiability.FinSat.IsWF
end Lax624099.FiniteSatisfiability.FinSat.IsWF

namespace Lax624099.FiniteSatisfiability.FinSat.gval
end Lax624099.FiniteSatisfiability.FinSat.gval

namespace Lax624099.FiniteSatisfiability.finsatRel.allN
end Lax624099.FiniteSatisfiability.finsatRel.allN

namespace Lax624099.FiniteSatisfiability.finsatRel.andN
end Lax624099.FiniteSatisfiability.finsatRel.andN

namespace Lax624099.FiniteSatisfiability.finsatRel.arg
end Lax624099.FiniteSatisfiability.finsatRel.arg

namespace Lax624099.FiniteSatisfiability.finsatRel.bind
end Lax624099.FiniteSatisfiability.finsatRel.bind

namespace Lax624099.FiniteSatisfiability.finsatRel.child
end Lax624099.FiniteSatisfiability.finsatRel.child

namespace Lax624099.FiniteSatisfiability.finsatRel.eqL
end Lax624099.FiniteSatisfiability.finsatRel.eqL

namespace Lax624099.FiniteSatisfiability.finsatRel.exN
end Lax624099.FiniteSatisfiability.finsatRel.exN

namespace Lax624099.FiniteSatisfiability.finsatRel.le
end Lax624099.FiniteSatisfiability.finsatRel.le

namespace Lax624099.FiniteSatisfiability.finsatRel.negL
end Lax624099.FiniteSatisfiability.finsatRel.negL

namespace Lax624099.FiniteSatisfiability.finsatRel.neqL
end Lax624099.FiniteSatisfiability.finsatRel.neqL

namespace Lax624099.FiniteSatisfiability.finsatRel.orN
end Lax624099.FiniteSatisfiability.finsatRel.orN

namespace Lax624099.FiniteSatisfiability.finsatRel.posL
end Lax624099.FiniteSatisfiability.finsatRel.posL

namespace Lax624099.FiniteSatisfiability.finsatRel.root
end Lax624099.FiniteSatisfiability.finsatRel.root

namespace Lax624099.FiniteSatisfiability.finsatRel.sig
end Lax624099.FiniteSatisfiability.finsatRel.sig
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

/-- `p` is a lowest position. -/
def MinPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le p q

/-- `q` is the next position above `p`. -/
def SuccPos (Le : A → A → Prop) (Posn : A → Prop) (p q : A) : Prop :=
  Posn p ∧ Posn q ∧ Le p q ∧ p ≠ q ∧ ∀ r, Posn r → Le p r → Le r q → r = p ∨ r = q

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

/-- The symbols a cell may initially hold: the input symbol where the input is
defined, the blank elsewhere. -/
def InitTape (p a : A) : Prop := M.Inp p a ∨ ((∀ b, ¬ M.Inp p b) ∧ M.Blank a)

/-- Well-formedness: the order is linear, there is a position to start on, the
input is functional, and there is exactly one blank symbol. -/
def WellFormed : Prop :=
  IsLinOrd M.Le ∧ (∃ p, M.Posn p) ∧
    (∀ p a b, M.Inp p a → M.Inp p b → a = b) ∧
    (∃ b, M.Blank b) ∧ (∀ a b, M.Blank a → M.Blank b → a = b)

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

/-- The position symbol. -/
abbrev tmPosn : turing.Relations 1 := .posn

/-- The transition symbol. -/
abbrev tmTr : turing.Relations 1 := .tr

/-- The start-state symbol. -/
abbrev tmStart : turing.Relations 1 := .start

/-- The accepting-state symbol. -/
abbrev tmAcc : turing.Relations 1 := .acc

/-- The blank symbol. -/
abbrev tmBlank : turing.Relations 1 := .blank

/-- The move-right symbol. -/
abbrev tmRight : turing.Relations 1 := .right

/-- The order symbol. -/
abbrev tmLe : turing.Relations 2 := .le

/-- The transition-source symbol. -/
abbrev tmSrc : turing.Relations 2 := .tsrc

/-- The transition-read symbol. -/
abbrev tmRead : turing.Relations 2 := .tread

/-- The transition-destination symbol. -/
abbrev tmDst : turing.Relations 2 := .tdst

/-- The transition-write symbol. -/
abbrev tmWrite : turing.Relations 2 := .twrite

/-- The input symbol. -/
abbrev tmInp : turing.Relations 2 := .inp

section Shorthands

variable [turing.Structure A]

/-- Being a position. -/
def TMPosn (a : A) : Prop := RelMap tmPosn ![a]

/-- Being a transition. -/
def TMTr (a : A) : Prop := RelMap tmTr ![a]

/-- Being a start state. -/
def TMStart (a : A) : Prop := RelMap tmStart ![a]

/-- Being an accepting state. -/
def TMAcc (a : A) : Prop := RelMap tmAcc ![a]

/-- Being the blank symbol. -/
def TMBlank (a : A) : Prop := RelMap tmBlank ![a]

/-- Moving the head right. -/
def TMRight (a : A) : Prop := RelMap tmRight ![a]

/-- The order on positions. -/
def TMLe (a b : A) : Prop := RelMap tmLe ![a, b]

/-- The state a transition applies in. -/
def TMSrc (a b : A) : Prop := RelMap tmSrc ![a, b]

/-- The symbol a transition reads. -/
def TMRead (a b : A) : Prop := RelMap tmRead ![a, b]

/-- The state a transition moves to. -/
def TMDst (a b : A) : Prop := RelMap tmDst ![a, b]

/-- The symbol a transition writes. -/
def TMWrite (a b : A) : Prop := RelMap tmWrite ![a, b]

/-- The initial contents of a cell. -/
def TMInp (a b : A) : Prop := RelMap tmInp ![a, b]

end Shorthands

/-- The machine an instance describes. -/
def tmData (A : Type) [turing.Structure A] : TMData A where
  Posn := TMPosn
  Le := TMLe
  Tr := TMTr
  Start := TMStart
  Acc := TMAcc
  Blank := TMBlank
  Right := TMRight
  Src := TMSrc
  Read := TMRead
  Dst := TMDst
  Write := TMWrite
  Inp := TMInp

end Lax904597.Machines
end

-- Lax624099.ConcreteInstances
section
namespace Lax624099.ConcreteInstances
end Lax624099.ConcreteInstances

namespace Lax624099.ConcreteInstances.DecisionProblem
end Lax624099.ConcreteInstances.DecisionProblem

namespace Lax624099.ConcreteInstances.FinStruct
end Lax624099.ConcreteInstances.FinStruct

namespace Lax624099.ConcreteInstances.FinVocab
end Lax624099.ConcreteInstances.FinVocab

namespace Lax624099.ConcreteInstances.tupleIdx
end Lax624099.ConcreteInstances.tupleIdx

namespace Lax624099.ConcreteInstances.FinStruct.equivProd
end Lax624099.ConcreteInstances.FinStruct.equivProd
end

-- Lax624099.Halting
section
namespace Lax624099.Halting

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Machines Lax624099.Problems

section Ripple

variable {A : Type} [Finite A] {Le : A → A → Prop} {Posn : A → Prop}

/-- `p` is a highest position. -/
def MaxPos (Le : A → A → Prop) (Posn : A → Prop) (p : A) : Prop :=
  Posn p ∧ ∀ q, Posn q → Le q p

end Ripple

/-- A configuration of a machine on an unbounded tape: the current state, the
cell the head is on, and the contents of every cell. A cell is a pair of a
*page* – an integer – and a position of the instance. -/
@[ext]
structure ConfigU (A : Type) where
  /-- The current state. -/
  state : A
  /-- The cell the head is on. -/
  head : ℤ × A
  /-- The symbol in each cell. -/
  tape : ℤ × A → A

namespace TMData

variable {A : Type} (M : TMData A)

/-- **The next cell**: one step along the order of the positions inside a page,
or the step from the last position of a page to the first position of the next
page. Since the pages are indexed by `ℤ`, every cell has a next one and a
previous one, on a well-formed machine with at least one position. -/
def SuccCell (c c' : ℤ × A) : Prop :=
  (c'.1 = c.1 ∧ SuccPos M.Le M.Posn c.2 c'.2) ∨
    (c'.1 = c.1 + 1 ∧ MaxPos M.Le M.Posn c.2 ∧ MinPos M.Le M.Posn c'.2)

/-- Being an initial configuration on an unbounded tape: a start state, the
head on the lowest position of page `0`, the input on page `0` and blanks
everywhere else. -/
def IsInitU (c : ConfigU A) : Prop :=
  M.Start c.state ∧ c.head.1 = 0 ∧ MinPos M.Le M.Posn c.head.2 ∧
    ∀ z p, M.Posn p →
      (z = 0 → M.InitTape p (c.tape (z, p))) ∧ (z ≠ 0 → M.Blank (c.tape (z, p)))

/-- **One step on an unbounded tape**: the clauses of
`DescriptiveComplexity.TMData.Step`, with `DescriptiveComplexity.TMData.SuccCell`
in place of `DescriptiveComplexity.SuccPos` for the move. -/
def StepU (c c' : ConfigU A) : Prop :=
  ∃ τ, M.Tr τ ∧ M.Src τ c.state ∧ M.Read τ (c.tape c.head) ∧
    M.Dst τ c'.state ∧ M.Write τ (c'.tape c.head) ∧
    (∀ x, x ≠ c.head → c'.tape x = c.tape x) ∧
    ((M.Right τ ∧ SuccCell M c.head c'.head) ∨
      (¬ M.Right τ ∧ SuccCell M c'.head c.head))

/-- Reaching one configuration from another in exactly `n` steps. -/
def StepsInU : ℕ → ConfigU A → ConfigU A → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ d, StepU M c d ∧ StepsInU n d c'

/-- **Acceptance on an unbounded tape**: some run from an initial configuration
reaches an accepting state, in any number of steps whatever.

This is `DescriptiveComplexity.TMData.Accepts` with the step bound dropped and
`DescriptiveComplexity.TMData.AcceptsSpace` with the space bound dropped: the
same `∃ n`, with nothing bounding it and nothing bounding the tape. A run is
still a finite object, so acceptance is an unbounded search over finite
witnesses – the shape of `∃SO[new]`, and the reason the halting problem is in
RE and in nothing smaller. -/
def AcceptsU : Prop :=
  ∃ (c₀ c : ConfigU A) (n : ℕ), IsInitU M c₀ ∧ StepsInU M n c₀ c ∧ M.Acc c.state

end TMData

/-- The machine described by the instance is well-formed and accepts its
input on an unbounded tape. -/
def HaltsOn (A : Type) [turing.Structure A] : Prop :=
  (tmData A).WellFormed ∧ TMData.AcceptsU (tmData A)

end Lax624099.Halting
end

-- Lax624099.PostCorrespondence
section
namespace Lax624099.PostCorrespondence
end Lax624099.PostCorrespondence

namespace Lax624099.PostCorrespondence.Pcp
end Lax624099.PostCorrespondence.Pcp

namespace Lax624099.PostCorrespondence.pcpRel
end Lax624099.PostCorrespondence.pcpRel

namespace Lax624099.PostCorrespondence.Pcp.IsWF
end Lax624099.PostCorrespondence.Pcp.IsWF

namespace Lax624099.PostCorrespondence.pcpRel.dom
end Lax624099.PostCorrespondence.pcpRel.dom

namespace Lax624099.PostCorrespondence.pcpRel.le
end Lax624099.PostCorrespondence.pcpRel.le

namespace Lax624099.PostCorrespondence.pcpRel.uAt
end Lax624099.PostCorrespondence.pcpRel.uAt

namespace Lax624099.PostCorrespondence.pcpRel.vAt
end Lax624099.PostCorrespondence.pcpRel.vAt
end

-- Lax624099.HaltingInvariance
section
namespace Lax624099.HaltingInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes

open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE

open Lax624099.FiniteSatisfiability

open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence

open Lax624099.ConcreteInstances

/-- The property `HaltsOn` is isomorphism-invariant. -/
axiom haltsOn_iso : ∀ {A B : Type} [turing.Structure A] [turing.Structure B],
  (A ≃[turing] B) → (HaltsOn A ↔ HaltsOn B)

end Lax624099.HaltingInvariance
end
