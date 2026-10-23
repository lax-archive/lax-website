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
namespace Lax564036
end Lax564036

namespace Lax564036.QuantifiedBooleanFormulas
end Lax564036.QuantifiedBooleanFormulas

namespace Lax564036.QuantifiedBooleanFormulas.QbfMatrix
end Lax564036.QuantifiedBooleanFormulas.QbfMatrix

namespace Lax564036.QuantifiedBooleanFormulas.altQuant
end Lax564036.QuantifiedBooleanFormulas.altQuant

namespace Lax564036.QuantifiedBooleanFormulas.qbfRel
end Lax564036.QuantifiedBooleanFormulas.qbfRel

namespace Lax564036.QuantifiedBooleanFormulas.qbfRel.block
end Lax564036.QuantifiedBooleanFormulas.qbfRel.block

namespace Lax564036.QuantifiedBooleanFormulas.qbfRel.isClause
end Lax564036.QuantifiedBooleanFormulas.qbfRel.isClause

namespace Lax564036.QuantifiedBooleanFormulas.qbfRel.negIn
end Lax564036.QuantifiedBooleanFormulas.qbfRel.negIn

namespace Lax564036.QuantifiedBooleanFormulas.qbfRel.posIn
end Lax564036.QuantifiedBooleanFormulas.qbfRel.posIn
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

open Lax904597.Sat

section Decode

variable {A : Type}

end Decode

open FirstOrder

namespace SatOcc

open Language Structure

variable {A : Type} [sat.Structure A]

/-- `c` is a clause. -/
def IsCl (c : A) : Prop := RelMap satIsClause ![c]

/-- `x` occurs positively in `c`. -/
def PosIn (c x : A) : Prop := RelMap satPosIn ![c, x]

/-- `x` occurs negatively in `c`. -/
def NegIn (c x : A) : Prop := RelMap satNegIn ![c, x]

/-- The literal `(x, s)` occurs in the clause `c` (`s = true` for a positive
occurrence). Occurrences are restricted to actual clauses, so that stray
`posIn`/`negIn` facts on non-clause elements do not create gadgets. -/
def OccIn (c x : A) (s : Bool) : Prop := IsCl c ∧ if s then PosIn c x else NegIn c x

end SatOcc

end Lax799700.Common
end

-- Lax799700.ThreeSat
section
namespace Lax799700.ThreeSat

open Lax799700.Common Lax904597.Sat

open FirstOrder

open Language Structure

section ThreeSat

variable (A : Type) [sat.Structure A]

/-- Every clause of a `Language.sat`-structure has at most three literal
occurrences: among any four occurrences of a clause, two coincide (as signed
occurrences). -/
def WidthAtMostThree : Prop :=
  ∀ (c : A) (x : Fin 4 → A) (s : Fin 4 → Bool),
    (∀ i, SatOcc.OccIn c (x i) (s i)) → ∃ i j, i ≠ j ∧ x i = x j ∧ s i = s j

end ThreeSat

open Lax904597.Problems Lax904597.Classes Lax799700.Problems

end Lax799700.ThreeSat
end

-- Lax564036.ThreeDnfTautology
section
namespace Lax564036.ThreeDnfTautology

open Lax904597.Problems Lax485149.Problems

open Lax799700.ThreeSat Lax564036.Tautology Lax904597.Sat

open FirstOrder

open Language Structure

section Problems

variable (A : Type) [sat.Structure A]

/-- An instance, read as a formula in conjunctive normal form,
is a yes-instance of 3-UNSAT if every clause has at most three literal
occurrences and no truth assignment satisfies the formula. This is the
CNF-side reading of `ThreeDnfTautology`; it is *not* the complement of 3SAT,
which also holds of wide instances. -/
def ThreeUnsatisfiable : Prop :=
  WidthAtMostThree A ∧ ¬Satisfiable A

end Problems

end Lax564036.ThreeDnfTautology
end

-- Lax564036.ThreeDnfTautologyInvariance
section
namespace Lax564036.ThreeDnfTautologyInvariance

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.SecondOrder

open Lax904597.Classes Lax904597.Sat Lax904597.Machines

open Lax485149.Problems Lax485149.Complement Lax535992.ClassPTIME

open Lax564036.Hierarchy Lax564036.Difference Lax564036.Tautology Lax564036.ThreeDnfTautology

open Lax564036.SatUnsat Lax564036.QuantifiedBooleanFormulas Lax564036.AlternatingMachines

/-- Being unsatisfiable of width at most three is isomorphism-invariant. -/
axiom threeUnsatisfiable_iso : ∀ {A B : Type} [sat.Structure A] [sat.Structure B],
  (A ≃[sat] B) → (ThreeUnsatisfiable A ↔ ThreeUnsatisfiable B)

end Lax564036.ThreeDnfTautologyInvariance
end
