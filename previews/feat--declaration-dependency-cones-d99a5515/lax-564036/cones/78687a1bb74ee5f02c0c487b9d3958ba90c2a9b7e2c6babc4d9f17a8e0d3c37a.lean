-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fin.Tuple.Basic
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
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
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

-- Lax485149.SecondOrderAtoms
section
namespace Lax485149
end Lax485149

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax485149.SecondOrderAtoms.SOAtom
end Lax485149.SecondOrderAtoms.SOAtom
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

-- Lax535992.ClassPTIME
section
namespace Lax535992.ClassPTIME
end Lax535992.ClassPTIME
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

-- Lax564036.AlternatingMachines
section
namespace Lax564036
end Lax564036

namespace Lax564036.AlternatingMachines
end Lax564036.AlternatingMachines

namespace Lax564036.AlternatingMachines.ATMData
end Lax564036.AlternatingMachines.ATMData

namespace Lax564036.AlternatingMachines.guardQ
end Lax564036.AlternatingMachines.guardQ

namespace Lax564036.AlternatingMachines.turingAltRel
end Lax564036.AlternatingMachines.turingAltRel

namespace Lax564036.AlternatingMachines.ATMData.AltAcc
end Lax564036.AlternatingMachines.ATMData.AltAcc

namespace Lax564036.AlternatingMachines.turingAltRel.base
end Lax564036.AlternatingMachines.turingAltRel.base

namespace Lax564036.AlternatingMachines.turingAltRel.blk
end Lax564036.AlternatingMachines.turingAltRel.blk
end

-- Lax564036.Difference
section
namespace Lax564036
end Lax564036

namespace Lax564036.Difference
end Lax564036.Difference
end

-- Lax564036.Hierarchy
section
namespace Lax564036
end Lax564036

namespace Lax564036.Hierarchy
end Lax564036.Hierarchy

namespace Lax564036.Hierarchy.SigmaP
end Lax564036.Hierarchy.SigmaP
end

-- Lax564036.QuantifiedBooleanFormulas
section
namespace Lax564036.QuantifiedBooleanFormulas

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of quantified Boolean formulas with `k`
quantifier blocks. -/
inductive qbfRel (k : ℕ) : ℕ → Type
  /-- `isClause c`: the element `c` is a clause (a term, for a disjunctive
  matrix). -/
  | isClause : qbfRel k 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : qbfRel k 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : qbfRel k 2
  /-- `block i x`: the variable `x` belongs to the `i`-th quantifier block. -/
  | block : Fin k → qbfRel k 1
  deriving DecidableEq

/-- The relational vocabulary of quantified Boolean formulas with `k`
quantifier blocks: that of CNF instances, together with `k` unary predicates
marking the variables of each quantifier block. -/
def qbf (k : ℕ) : Language :=
  ⟨fun _ => Empty, qbfRel k⟩

variable {k : ℕ}

/-- The symbol for “is a clause”. -/
abbrev qbfIsClause : (qbf k).Relations 1 := .isClause

/-- The symbol for “occurs positively in”. -/
abbrev qbfPosIn : (qbf k).Relations 2 := .posIn

/-- The symbol for “occurs negatively in”. -/
abbrev qbfNegIn : (qbf k).Relations 2 := .negIn

/-- The symbol marking the variables of the `i`-th quantifier block. -/
abbrev qbfBlock (i : Fin k) : (qbf k).Relations 1 := .block i

open FirstOrder

open Language Structure

/-- Alternating quantification over `k` truth assignments on `A`: the
assignment of index `0` is quantified outermost, existentially if `pol` is
`true`, and the polarities alternate inwards. -/
def altQuant (A : Type) : ∀ (k : ℕ), ((Fin k → A → Prop) → Prop) → Bool → Prop
  | 0, P, _ => P Fin.elim0
  | k + 1, P, true => ∃ ν : A → Prop, altQuant A k (fun νs => P (Fin.cons ν νs)) false
  | k + 1, P, false => ∀ ν : A → Prop, altQuant A k (fun νs => P (Fin.cons ν νs)) true

section Matrix

variable {k : ℕ} {A : Type} [(qbf k).Structure A]

/-- The truth value of the variable `x` under a tuple of block assignments:
`x` is true when some block marking it assigns it the value true. (In a
well-formed instance the block marks partition the variables, so exactly one
assignment is consulted.) -/
def qbfVal (νs : Fin k → A → Prop) (x : A) : Prop :=
  ∃ i : Fin k, RelMap (qbfBlock i) ![x] ∧ νs i x

/-- Conjunctive satisfaction, with the sign of every literal flipped when
`swap` is `true`: every clause then has to contain a literal that the block
assignments make *false*. -/
def CnfSatWith (swap : Bool) (νs : Fin k → A → Prop) : Prop :=
  ∀ c : A, RelMap (qbfIsClause (k := k)) ![c] →
    ∃ x : A,
      (RelMap (if swap then qbfNegIn (k := k) else qbfPosIn (k := k)) ![c, x] ∧ qbfVal νs x) ∨
      (RelMap (if swap then qbfPosIn (k := k) else qbfNegIn (k := k)) ![c, x] ∧ ¬qbfVal νs x)

/-- The conjunctive matrix: every clause contains a literal made true by the
block assignments. -/
abbrev CnfSat (νs : Fin k → A → Prop) : Prop := CnfSatWith false νs

/-- The disjunctive matrix: some term has all of its literals made true by the
block assignments. -/
def DnfSat (νs : Fin k → A → Prop) : Prop :=
  ∃ c : A, RelMap (qbfIsClause (k := k)) ![c] ∧
    ∀ x : A, (RelMap (qbfPosIn (k := k)) ![c, x] → qbfVal νs x) ∧
      (RelMap (qbfNegIn (k := k)) ![c, x] → ¬qbfVal νs x)

/-- The matrix of a quantified Boolean formula: conjunctive when `cnf` is
`true`, disjunctive when it is `false`. -/
def QbfMatrix (cnf : Bool) (νs : Fin k → A → Prop) : Prop :=
  match cnf with
  | true => CnfSat νs
  | false => DnfSat νs

end Matrix

end Lax564036.QuantifiedBooleanFormulas
end

-- Lax564036.SatUnsat
section
namespace Lax564036
end Lax564036

namespace Lax564036.SatUnsat
end Lax564036.SatUnsat

namespace Lax564036.SatUnsat.satPairRel
end Lax564036.SatUnsat.satPairRel

namespace Lax564036.SatUnsat.satPairRel.isClause₁
end Lax564036.SatUnsat.satPairRel.isClause₁

namespace Lax564036.SatUnsat.satPairRel.isClause₂
end Lax564036.SatUnsat.satPairRel.isClause₂

namespace Lax564036.SatUnsat.satPairRel.negIn₁
end Lax564036.SatUnsat.satPairRel.negIn₁

namespace Lax564036.SatUnsat.satPairRel.negIn₂
end Lax564036.SatUnsat.satPairRel.negIn₂

namespace Lax564036.SatUnsat.satPairRel.posIn₁
end Lax564036.SatUnsat.satPairRel.posIn₁

namespace Lax564036.SatUnsat.satPairRel.posIn₂
end Lax564036.SatUnsat.satPairRel.posIn₂
end

-- Lax904597.Sat
section
namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.Sat.satRel
end Lax904597.Sat.satRel

namespace Lax904597.Sat.satRel.isClause
end Lax904597.Sat.satRel.isClause

namespace Lax904597.Sat.satRel.negIn
end Lax904597.Sat.satRel.negIn

namespace Lax904597.Sat.satRel.posIn
end Lax904597.Sat.satRel.posIn
end

-- Lax564036.Tautology
section
namespace Lax564036
end Lax564036

namespace Lax564036.Tautology
end Lax564036.Tautology
end

-- Lax799700.Problems
section
namespace Lax799700
end Lax799700

namespace Lax799700.Problems
end Lax799700.Problems

namespace Lax799700.Problems.DecisionProblem
end Lax799700.Problems.DecisionProblem

namespace Lax799700.Problems.DecisionProblem.ofPred
end Lax799700.Problems.DecisionProblem.ofPred
end

-- Lax799700.Common
section
namespace Lax799700.Common
end Lax799700.Common

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc
end

-- Lax799700.ThreeSat
section
namespace Lax799700.ThreeSat
end Lax799700.ThreeSat
end

-- Lax564036.ThreeDnfTautology
section
namespace Lax564036.ThreeDnfTautology
end Lax564036.ThreeDnfTautology
end

-- Lax564036.QuantifiedBooleanFormulasInvariance
section
namespace Lax564036.QuantifiedBooleanFormulasInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes Lax904597.Sat Lax904597.Machines

open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME

open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology

open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- The truth of a quantified Boolean formula is isomorphism-invariant. -/
axiom qbfTrue_iso : ∀ (k : ℕ) (start cnf : Bool) {A B : Type} [(qbf k).Structure A]
  [(qbf k).Structure B], (A ≃[qbf k] B) →
    (altQuant A k (fun νs => QbfMatrix cnf νs) start ↔
      altQuant B k (fun νs => QbfMatrix cnf νs) start)

end Lax564036.QuantifiedBooleanFormulasInvariance
end
