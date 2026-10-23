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

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of Post correspondence systems. -/
inductive pcpRel : ℕ → Type
  /-- `le x y`: the order of the positions. -/
  | le : pcpRel 2
  /-- `dom d`: the element `d` is one of the dominoes. -/
  | dom : pcpRel 1
  /-- `uAt d p c`: the top word of the domino `d` has the letter `c` at the
  position `p`. -/
  | uAt : pcpRel 3
  /-- `vAt d p c`: the bottom word of the domino `d` has the letter `c` at the
  position `p`. -/
  | vAt : pcpRel 3
  deriving DecidableEq

/-- The relational vocabulary of Post correspondence systems: marked dominoes
carrying two words each, over a universe ordered by the order of the positions
of those words. -/
def pcp : Language :=
  ⟨fun _ => Empty, pcpRel⟩

/-- The order symbol of the positions. -/
abbrev pcpLeSym : pcp.Relations 2 := .le

/-- The symbol marking the dominoes. -/
abbrev pcpDomSym : pcp.Relations 1 := .dom

/-- The symbol giving the letters of the top words. -/
abbrev pcpUSym : pcp.Relations 3 := .uAt

/-- The symbol giving the letters of the bottom words. -/
abbrev pcpVSym : pcp.Relations 3 := .vAt

open FirstOrder

open Language Structure

namespace Pcp

section Reading

variable {A : Type} [pcp.Structure A]

/-- `x` precedes `y` in the order of the positions. -/
def Ord (x y : A) : Prop := RelMap pcpLeSym ![x, y]

/-- `x` strictly precedes `y` in the order of the positions. -/
def OrdLt (x y : A) : Prop := Ord x y ∧ x ≠ y

/-- The element `d` is one of the dominoes. -/
def DomG (d : A) : Prop := RelMap pcpDomSym ![d]

/-- The top word of the domino `d` has the letter `c` at the position `p`. -/
def UAt (d p c : A) : Prop := RelMap pcpUSym ![d, p, c]

/-- The bottom word of the domino `d` has the letter `c` at the position
`p`. -/
def VAt (d p c : A) : Prop := RelMap pcpVSym ![d, p, c]

/-- The position `p` carries a letter of the top word of the domino `d`. -/
def UsedU (d p : A) : Prop := ∃ c, UAt d p c

/-- The position `p` carries a letter of the bottom word of the domino `d`. -/
def UsedV (d p : A) : Prop := ∃ c, VAt d p c

end Reading

/-- **Well-formedness of a Post correspondence system**: the order symbol is a
linear order, and each domino carries at most one letter at each position of
each of its two words. -/
structure IsWF (A : Type) [pcp.Structure A] : Prop where
  /-- The order of the positions is reflexive. -/
  ord_refl : ∀ x : A, Ord x x
  /-- The order of the positions is transitive. -/
  ord_trans : ∀ x y z : A, Ord x y → Ord y z → Ord x z
  /-- The order of the positions is antisymmetric. -/
  ord_antisymm : ∀ x y : A, Ord x y → Ord y x → x = y
  /-- The order of the positions is total. -/
  ord_total : ∀ x y : A, Ord x y ∨ Ord y x
  /-- A top word has at most one letter at each position. -/
  uAt_fun : ∀ d p c c' : A, UAt d p c → UAt d p c' → c = c'
  /-- A bottom word has at most one letter at each position. -/
  vAt_fun : ∀ d p c c' : A, VAt d p c → VAt d p c' → c = c'

section Words

variable {A : Type} [pcp.Structure A]

/-- **The top word of the domino `d` is `w`**: some strictly increasing list
enumerates exactly the positions used by the top word of `d`, and `w` carries
the letters at them. -/
def IsWordU (d : A) (w : List A) : Prop :=
  ∃ ps : List A, ps.Pairwise OrdLt ∧ (∀ p, p ∈ ps ↔ UsedU d p) ∧ List.Forall₂ (UAt d) ps w

/-- **The bottom word of the domino `d` is `w`**, as in
`DescriptiveComplexity.Pcp.IsWordU`. -/
def IsWordV (d : A) (w : List A) : Prop :=
  ∃ ps : List A, ps.Pairwise OrdLt ∧ (∀ p, p ∈ ps ↔ UsedV d p) ∧ List.Forall₂ (VAt d) ps w

end Words

/-- **The system has a match**: the instance is well-formed and there is a
nonempty sequence of dominoes whose top words and whose bottom words have the
same concatenation. -/
def PcpOn (A : Type) [pcp.Structure A] : Prop :=
  IsWF A ∧ ∃ (l : List A) (us vs : List (List A)),
    l ≠ [] ∧ (∀ d ∈ l, DomG d) ∧
      List.Forall₂ IsWordU l us ∧ List.Forall₂ IsWordV l vs ∧ us.flatten = vs.flatten

end Pcp

open Lax904597.Problems Lax624099.Problems

end Lax624099.PostCorrespondence
end

-- Lax624099.PostCorrespondenceInvariance
section
namespace Lax624099.PostCorrespondenceInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes

open Lax904597.Machines Lax624099.Problems Lax624099.ValueInvention Lax624099.ClassRE

open Lax624099.FiniteSatisfiability

open Lax624099.Halting Lax624099.CodeHalting Lax624099.PostCorrespondence

open Lax624099.ConcreteInstances

/-- The property `Pcp.PcpOn` is isomorphism-invariant. -/
axiom pcpOn_iso : ∀ {A B : Type} [pcp.Structure A] [pcp.Structure B],
  (A ≃[pcp] B) → (Pcp.PcpOn A ↔ Pcp.PcpOn B)

end Lax624099.PostCorrespondenceInvariance
end
