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

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of code instances. -/
inductive codeRel : ℕ → Type
  /-- `croot n`: `n` is the root of the syntax tree. -/
  | croot : codeRel 1
  /-- `czero n`: `n` draws the constructor `zero`. -/
  | czero : codeRel 1
  /-- `csucc n`: `n` draws the constructor `succ`. -/
  | csucc : codeRel 1
  /-- `cleft n`: `n` draws the constructor `left`. -/
  | cleft : codeRel 1
  /-- `cright n`: `n` draws the constructor `right`. -/
  | cright : codeRel 1
  /-- `cpair n`: `n` draws the constructor `pair`. -/
  | cpair : codeRel 1
  /-- `ccomp n`: `n` draws the constructor `comp`. -/
  | ccomp : codeRel 1
  /-- `cprec n`: `n` draws the constructor `prec`. -/
  | cprec : codeRel 1
  /-- `crfind n`: `n` draws the constructor `rfind'`. -/
  | crfind : codeRel 1
  /-- `carg1 n m`: `m` is the first child of `n`. -/
  | carg1 : codeRel 2
  /-- `carg2 n m`: `m` is the second child of `n`. -/
  | carg2 : codeRel 2
  deriving DecidableEq

/-- The relational language of code instances: the eight constructor marks,
the mark of the root, and the two child relations. -/
def code : Language :=
  ⟨fun _ => Empty, codeRel⟩

/-- The root symbol. -/
abbrev cRoot : code.Relations 1 := .croot

/-- The `zero` symbol. -/
abbrev cZero : code.Relations 1 := .czero

/-- The `succ` symbol. -/
abbrev cSucc : code.Relations 1 := .csucc

/-- The `left` symbol. -/
abbrev cLeft : code.Relations 1 := .cleft

/-- The `right` symbol. -/
abbrev cRight : code.Relations 1 := .cright

/-- The `pair` symbol. -/
abbrev cPair : code.Relations 1 := .cpair

/-- The `comp` symbol. -/
abbrev cComp : code.Relations 1 := .ccomp

/-- The `prec` symbol. -/
abbrev cPrec : code.Relations 1 := .cprec

/-- The `rfind'` symbol. -/
abbrev cRfind : code.Relations 1 := .crfind

/-- The first-child symbol. -/
abbrev cArg1 : code.Relations 2 := .carg1

/-- The second-child symbol. -/
abbrev cArg2 : code.Relations 2 := .carg2

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [code.Structure A]

/-- Being the root. -/
def CRoot (a : A) : Prop := RelMap cRoot ![a]

/-- Drawing the constructor `zero`. -/
def CZero (a : A) : Prop := RelMap cZero ![a]

/-- Drawing the constructor `succ`. -/
def CSucc (a : A) : Prop := RelMap cSucc ![a]

/-- Drawing the constructor `left`. -/
def CLeft (a : A) : Prop := RelMap cLeft ![a]

/-- Drawing the constructor `right`. -/
def CRight (a : A) : Prop := RelMap cRight ![a]

/-- Drawing the constructor `pair`. -/
def CPair (a : A) : Prop := RelMap cPair ![a]

/-- Drawing the constructor `comp`. -/
def CComp (a : A) : Prop := RelMap cComp ![a]

/-- Drawing the constructor `prec`. -/
def CPrec (a : A) : Prop := RelMap cPrec ![a]

/-- Drawing the constructor `rfind'`. -/
def CRfind (a : A) : Prop := RelMap cRfind ![a]

/-- Being the first child. -/
def CArg1 (a b : A) : Prop := RelMap cArg1 ![a, b]

/-- Being the second child. -/
def CArg2 (a b : A) : Prop := RelMap cArg2 ![a, b]

end Shorthands

section Decode

variable {A : Type} [code.Structure A]

/-- **The node `n` draws the code `c`.** A recursion on the code: the mark of
the node must be the constructor's, and its children must draw the
constructor's arguments. -/
def DecodesTo (n : A) : Nat.Partrec.Code → Prop
  | .zero => CZero n
  | .succ => CSucc n
  | .left => CLeft n
  | .right => CRight n
  | .pair cf cg =>
      CPair n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .comp cf cg =>
      CComp n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .prec cf cg =>
      CPrec n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .rfind' cf => CRfind n ∧ ∃ a, CArg1 n a ∧ DecodesTo a cf

end Decode

open Lax904597.Problems Lax624099.Problems

/-- The root of the instance draws a code halting on `0`. -/
def CodeHaltsOn (A : Type) [code.Structure A] : Prop :=
  ∃ (n : A) (c : Nat.Partrec.Code), CRoot n ∧ DecodesTo n c ∧ (Nat.Partrec.Code.eval c 0).Dom

end Lax624099.CodeHalting
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
namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.Machines.Config
end Lax904597.Machines.Config

namespace Lax904597.Machines.TMData
end Lax904597.Machines.TMData

namespace Lax904597.Machines.turingRel
end Lax904597.Machines.turingRel

namespace Lax904597.Machines.Config.ext
end Lax904597.Machines.Config.ext

namespace Lax904597.Machines.TMData.StepsIn
end Lax904597.Machines.TMData.StepsIn

namespace Lax904597.Machines.turingRel.acc
end Lax904597.Machines.turingRel.acc

namespace Lax904597.Machines.turingRel.blank
end Lax904597.Machines.turingRel.blank

namespace Lax904597.Machines.turingRel.inp
end Lax904597.Machines.turingRel.inp

namespace Lax904597.Machines.turingRel.le
end Lax904597.Machines.turingRel.le

namespace Lax904597.Machines.turingRel.posn
end Lax904597.Machines.turingRel.posn

namespace Lax904597.Machines.turingRel.right
end Lax904597.Machines.turingRel.right

namespace Lax904597.Machines.turingRel.start
end Lax904597.Machines.turingRel.start

namespace Lax904597.Machines.turingRel.tdst
end Lax904597.Machines.turingRel.tdst

namespace Lax904597.Machines.turingRel.tr
end Lax904597.Machines.turingRel.tr

namespace Lax904597.Machines.turingRel.tread
end Lax904597.Machines.turingRel.tread

namespace Lax904597.Machines.turingRel.tsrc
end Lax904597.Machines.turingRel.tsrc

namespace Lax904597.Machines.turingRel.twrite
end Lax904597.Machines.turingRel.twrite
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
end Lax624099.Halting

namespace Lax624099.Halting.ConfigU
end Lax624099.Halting.ConfigU

namespace Lax624099.Halting.TMData
end Lax624099.Halting.TMData

namespace Lax624099.Halting.ConfigU.ext
end Lax624099.Halting.ConfigU.ext

namespace Lax624099.Halting.TMData.StepsInU
end Lax624099.Halting.TMData.StepsInU
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

-- Lax624099.CodeHaltingInvariance
section
namespace Lax624099.CodeHaltingInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes

open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE

open Lax624099.FiniteSatisfiability

open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence

open Lax624099.ConcreteInstances

/-- The property `CodeHaltsOn` is isomorphism-invariant. -/
axiom codeHaltsOn_iso : ∀ {A B : Type} [code.Structure A] [code.Structure B],
  (A ≃[code] B) → (CodeHaltsOn A ↔ CodeHaltsOn B)

end Lax624099.CodeHaltingInvariance
end
