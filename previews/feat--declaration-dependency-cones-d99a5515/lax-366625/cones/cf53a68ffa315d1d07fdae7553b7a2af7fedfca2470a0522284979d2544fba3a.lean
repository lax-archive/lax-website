-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.Order.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
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

-- Lax366625.CountingProblems
section
namespace Lax366625
end Lax366625

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.CountingProblems.CountingProblem
end Lax366625.CountingProblems.CountingProblem

namespace Lax366625.CountingProblems.OrderedParsimoniousReduction
end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax366625.CountingProblems.ParsimoniousReduction
end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction
end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax366625.CountingProblems.CountingProblem.ofFun
end Lax366625.CountingProblems.CountingProblem.ofFun
end

-- Lax366625.CountingClasses
section
namespace Lax366625.CountingClasses
end Lax366625.CountingClasses

namespace Lax366625.CountingClasses.CountingClass
end Lax366625.CountingClasses.CountingClass
end

-- Lax485149.Problems
section
namespace Lax485149
end Lax485149

namespace Lax485149.Problems
end Lax485149.Problems

namespace Lax485149.Problems.DecisionProblem
end Lax485149.Problems.DecisionProblem

namespace Lax485149.Problems.DecisionProblem.ofPred
end Lax485149.Problems.DecisionProblem.ofPred
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

-- Lax535992.DeterministicMachines
section
namespace Lax535992
end Lax535992

namespace Lax535992.DeterministicMachines
end Lax535992.DeterministicMachines

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData
end

-- Lax366625.MachineNumbers
section
namespace Lax366625.MachineNumbers
end Lax366625.MachineNumbers

namespace Lax366625.MachineNumbers.TMData
end Lax366625.MachineNumbers.TMData

namespace Lax366625.MachineNumbers.tapeOutRel
end Lax366625.MachineNumbers.tapeOutRel

namespace Lax366625.MachineNumbers.tapeOutRel.one
end Lax366625.MachineNumbers.tapeOutRel.one

namespace Lax366625.MachineNumbers.tapeOutRel.out
end Lax366625.MachineNumbers.tapeOutRel.out
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

-- Lax366625.CountingRuns
section
namespace Lax366625.CountingRuns
end Lax366625.CountingRuns

namespace Lax366625.CountingRuns.TMData
end Lax366625.CountingRuns.TMData
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

/-- `isClause c`: the element `c` is a clause. -/
abbrev satIsClause : sat.Relations 1 := .isClause

/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
abbrev satPosIn : sat.Relations 2 := .posIn

/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
abbrev satNegIn : sat.Relations 2 := .negIn

/-- A CNF instance is satisfiable if some assignment of truth values to its
elements makes every clause contain a true literal. -/
def Satisfiable (A : Type) [sat.Structure A] : Prop :=
  ∃ ν : A → Prop, ∀ c : A, RelMap satIsClause ![c] →
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)

end Lax904597.Sat
end

-- Lax366625.CountingSat
section
namespace Lax366625.CountingSat
end Lax366625.CountingSat
end

-- Lax535992.HornSat
section
namespace Lax535992.HornSat

open Lax904597.Problems Lax485149.Problems

open Lax904597.Sat

open FirstOrder

open Language Structure

section HornSat

variable (A : Type) [sat.Structure A]

/-- Every clause of a CNF instance has at most one positive
literal: any two variables occurring positively in the same clause coincide. -/
def AtMostOnePositive : Prop :=
  ∀ c x y : A, RelMap satIsClause ![c] → RelMap satPosIn ![c, x] →
    RelMap satPosIn ![c, y] → x = y

/-- A CNF instance is a yes-instance of HORN-SAT if every clause
has at most one positive literal and the CNF is satisfiable. -/
def HornSatisfiable : Prop :=
  AtMostOnePositive A ∧ Satisfiable A

end HornSat

end Lax535992.HornSat
end

-- Lax366625.HornNumbers
section
namespace Lax366625.HornNumbers

open Lax535992.HornSat Lax904597.Sat

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section LeastModel

variable {A : Type} [sat.Structure A]

/-- The stages of unit propagation: `ForcedIn n x` says that `x` is the
positive literal of a clause whose negative literals are all forced in fewer
than `n` rounds. -/
def ForcedIn : ℕ → A → Prop
  | 0, _ => False
  | n + 1, x => ∃ c : A, RelMap satIsClause ![c] ∧ RelMap satPosIn ![c, x] ∧
      ∀ y : A, RelMap satNegIn ![c, y] → ForcedIn n y

/-- A variable is *forced* when some stage forces it. On a Horn formula this
is the least model of the implications. -/
def Forced (x : A) : Prop := ∃ n, ForcedIn n x

end LeastModel

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive digitOrderRel : ℕ → Type where
/-- `out x`: the element `x` holds one digit. -/
  | out : digitOrderRel 1
/-- `below y x`: the digit of `y` is at most as significant as the one of
  `x`. -/
  | below : digitOrderRel 2
  deriving DecidableEq

/-- The symbols reading a number off a set of marked elements. -/
def digitOrder : FirstOrder.Language :=
  ⟨fun _ => Empty, digitOrderRel⟩

/-- `out x`: the element `x` holds one digit. -/
abbrev dgoOut : digitOrder.Relations 1 :=
  .out

/-- `below y x`: the digit of `y` is at most as significant as the one of
  `x`. -/
abbrev dgoBelow : digitOrder.Relations 2 :=
  .below

/-- The relational language of Horn formulas writing a number. -/
abbrev satOut : Language.{0, 0} := sat.sum digitOrder

open FirstOrder

open Language Structure

/-- “Is an output variable”. -/
abbrev hnOut : satOut.Relations 1 := Sum.inr dgoOut

/-- The comparison of the output variables. -/
abbrev hnBelow : satOut.Relations 2 := Sum.inr dgoBelow

/-- A Horn formula writing a number is a CNF instance. -/
instance satOutStructure (A : Type) [satOut.Structure A] :
    sat.Structure A :=
  (LHom.sumInl : sat →ᴸ satOut).reduct A

section Semantics

variable {A : Type} [satOut.Structure A]

/-- The output variable `x` is forced. -/
def ForcedDigit (x : A) : Prop :=
  RelMap hnOut ![x] ∧ Forced x

/-- `y` is an output variable strictly below `x`. -/
def LowerVar (x y : A) : Prop :=
  RelMap hnOut ![y] ∧ y ≠ x ∧ RelMap hnBelow ![y, x]

/-- The rank of a variable among the outputs: the number of output variables
strictly below it. -/
noncomputable def varRank (x : A) : ℕ :=
  Nat.card {y : A // LowerVar x y}

variable (A) in
/-- **The comparison of the outputs is a linear order on them**: reflexive,
transitive, antisymmetric and total among the output variables. -/
def VarOrder : Prop :=
  (∀ p : A, RelMap hnOut ![p] → RelMap hnBelow ![p, p]) ∧
    (∀ p q r : A, RelMap hnOut ![p] → RelMap hnOut ![q] → RelMap hnOut ![r] →
      RelMap hnBelow ![p, q] → RelMap hnBelow ![q, r] → RelMap hnBelow ![p, r]) ∧
    (∀ p q : A, RelMap hnOut ![p] → RelMap hnOut ![q] →
      RelMap hnBelow ![p, q] → RelMap hnBelow ![q, p] → p = q) ∧
    ∀ p q : A, RelMap hnOut ![p] → RelMap hnOut ![q] →
      RelMap hnBelow ![p, q] ∨ RelMap hnBelow ![q, p]

variable (A) in
open Classical in
/-- **The number written by unit propagation**: each forced output variable
contributes two to the power of its rank among the outputs. Instances that are
not satisfiable Horn formulas, or whose outputs are not linearly ordered,
write `0`. -/
noncomputable def hornNumber : ℕ :=
  if HornSatisfiable A ∧ VarOrder A then ∑ᶠ x : A, if ForcedDigit x then 2 ^ varRank x else 0
  else 0

end Semantics

open Lax366625.CountingProblems

end Lax366625.HornNumbers
end

-- Lax535992.CircuitValue
section
namespace Lax535992
end Lax535992

namespace Lax535992.CircuitValue
end Lax535992.CircuitValue

namespace Lax535992.CircuitValue.GateVal
end Lax535992.CircuitValue.GateVal

namespace Lax535992.CircuitValue.circuitRel
end Lax535992.CircuitValue.circuitRel

namespace Lax535992.CircuitValue.circuitRel.isAnd
end Lax535992.CircuitValue.circuitRel.isAnd

namespace Lax535992.CircuitValue.circuitRel.isFalse
end Lax535992.CircuitValue.circuitRel.isFalse

namespace Lax535992.CircuitValue.circuitRel.isNot
end Lax535992.CircuitValue.circuitRel.isNot

namespace Lax535992.CircuitValue.circuitRel.isOr
end Lax535992.CircuitValue.circuitRel.isOr

namespace Lax535992.CircuitValue.circuitRel.isTrue
end Lax535992.CircuitValue.circuitRel.isTrue

namespace Lax535992.CircuitValue.circuitRel.left
end Lax535992.CircuitValue.circuitRel.left

namespace Lax535992.CircuitValue.circuitRel.out
end Lax535992.CircuitValue.circuitRel.out

namespace Lax535992.CircuitValue.circuitRel.right
end Lax535992.CircuitValue.circuitRel.right
end

-- Lax366625.NumberedCircuits
section
namespace Lax366625.NumberedCircuits
end Lax366625.NumberedCircuits

namespace Lax366625.NumberedCircuits.circuitOfNum
end Lax366625.NumberedCircuits.circuitOfNum

namespace Lax366625.NumberedCircuits.numCircuitRel
end Lax366625.NumberedCircuits.numCircuitRel

namespace Lax366625.NumberedCircuits.numCircuitRel.below
end Lax366625.NumberedCircuits.numCircuitRel.below

namespace Lax366625.NumberedCircuits.numCircuitRel.isAnd
end Lax366625.NumberedCircuits.numCircuitRel.isAnd

namespace Lax366625.NumberedCircuits.numCircuitRel.isFalse
end Lax366625.NumberedCircuits.numCircuitRel.isFalse

namespace Lax366625.NumberedCircuits.numCircuitRel.isNot
end Lax366625.NumberedCircuits.numCircuitRel.isNot

namespace Lax366625.NumberedCircuits.numCircuitRel.isOr
end Lax366625.NumberedCircuits.numCircuitRel.isOr

namespace Lax366625.NumberedCircuits.numCircuitRel.isTrue
end Lax366625.NumberedCircuits.numCircuitRel.isTrue

namespace Lax366625.NumberedCircuits.numCircuitRel.left
end Lax366625.NumberedCircuits.numCircuitRel.left

namespace Lax366625.NumberedCircuits.numCircuitRel.out
end Lax366625.NumberedCircuits.numCircuitRel.out

namespace Lax366625.NumberedCircuits.numCircuitRel.right
end Lax366625.NumberedCircuits.numCircuitRel.right
end

-- Lax485149.SecondOrderAtoms
section
namespace Lax485149
end Lax485149

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax485149.SecondOrderAtoms.SOAtom
end Lax485149.SecondOrderAtoms.SOAtom
end

-- Lax535992.HornFragment
section
namespace Lax535992
end Lax535992

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.HornFragment.HornClause
end Lax535992.HornFragment.HornClause

namespace Lax535992.HornFragment.HornProgram
end Lax535992.HornFragment.HornProgram
end

-- Lax535992.LeastFixedPoint
section
namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax535992.LeastFixedPoint.Derives
end Lax535992.LeastFixedPoint.Derives

namespace Lax535992.LeastFixedPoint.LFPDef
end Lax535992.LeastFixedPoint.LFPDef
end

-- Lax895169.BitPredicate
section
namespace Lax895169
end Lax895169

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax895169.BitPredicate.prefixHolds
end Lax895169.BitPredicate.prefixHolds
end

-- Lax366625.QuantitativeLogic
section
namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax366625.QuantitativeLogic.DigitLFPDef
end Lax366625.QuantitativeLogic.DigitLFPDef

namespace Lax366625.QuantitativeLogic.QLFPDef
end Lax366625.QuantitativeLogic.QLFPDef

namespace Lax366625.QuantitativeLogic.QTerm
end Lax366625.QuantitativeLogic.QTerm

namespace Lax366625.QuantitativeLogic.QTerm.add
end Lax366625.QuantitativeLogic.QTerm.add

namespace Lax366625.QuantitativeLogic.QTerm.const
end Lax366625.QuantitativeLogic.QTerm.const

namespace Lax366625.QuantitativeLogic.QTerm.eval
end Lax366625.QuantitativeLogic.QTerm.eval

namespace Lax366625.QuantitativeLogic.QTerm.ind
end Lax366625.QuantitativeLogic.QTerm.ind

namespace Lax366625.QuantitativeLogic.QTerm.mul
end Lax366625.QuantitativeLogic.QTerm.mul

namespace Lax366625.QuantitativeLogic.QTerm.prod
end Lax366625.QuantitativeLogic.QTerm.prod

namespace Lax366625.QuantitativeLogic.QTerm.sum
end Lax366625.QuantitativeLogic.QTerm.sum
end

-- Lax366625.SecondOrderCounting
section
namespace Lax366625.SecondOrderCounting
end Lax366625.SecondOrderCounting

namespace Lax366625.SecondOrderCounting.SQTerm
end Lax366625.SecondOrderCounting.SQTerm

namespace Lax366625.SecondOrderCounting.SQTerm.add
end Lax366625.SecondOrderCounting.SQTerm.add

namespace Lax366625.SecondOrderCounting.SQTerm.const
end Lax366625.SecondOrderCounting.SQTerm.const

namespace Lax366625.SecondOrderCounting.SQTerm.eval
end Lax366625.SecondOrderCounting.SQTerm.eval

namespace Lax366625.SecondOrderCounting.SQTerm.ind
end Lax366625.SecondOrderCounting.SQTerm.ind

namespace Lax366625.SecondOrderCounting.SQTerm.mul
end Lax366625.SecondOrderCounting.SQTerm.mul

namespace Lax366625.SecondOrderCounting.SQTerm.prod
end Lax366625.SecondOrderCounting.SQTerm.prod

namespace Lax366625.SecondOrderCounting.SQTerm.sosum
end Lax366625.SecondOrderCounting.SQTerm.sosum

namespace Lax366625.SecondOrderCounting.SQTerm.sum
end Lax366625.SecondOrderCounting.SQTerm.sum
end

-- Lax366625.WitnessCounting
section
namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting
end

-- Lax485149.Complement
section
namespace Lax485149
end Lax485149

namespace Lax485149.Complement
end Lax485149.Complement

namespace Lax485149.Complement.DecisionProblem
end Lax485149.Complement.DecisionProblem
end

-- Lax904597.Classes
section
namespace Lax904597.Classes
end Lax904597.Classes

namespace Lax904597.Classes.ComplexityClass
end Lax904597.Classes.ComplexityClass
end

-- Lax535992.ClassPTIME
section
namespace Lax535992.ClassPTIME
end Lax535992.ClassPTIME
end

-- Lax366625.NumbersValue
section
namespace Lax366625.NumbersValue

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes Lax904597.Sat Lax904597.Machines

open Lax535992.ClassPTIME

open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting

open Lax366625.SecondOrderCounting

open Lax366625.QuantitativeLogic Lax366625.CountingSat Lax366625.MachineNumbers

open Lax366625.CountingRuns

open Lax366625.NumberedCircuits Lax366625.HornNumbers

/-- The number written by unit propagation is isomorphism-invariant. -/
axiom hornNumber_count_iso : ∀ {A B : Type} [satOut.Structure A] [satOut.Structure B],
  (A ≃[satOut] B) → hornNumber A = hornNumber B

end Lax366625.NumbersValue
end
