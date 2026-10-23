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
namespace Lax624099.ConcreteInstances.DecisionProblem
end Lax624099.ConcreteInstances.DecisionProblem

namespace Lax624099.ConcreteInstances.FinStruct.equivProd
end Lax624099.ConcreteInstances.FinStruct.equivProd

namespace Lax624099.ConcreteInstances

open Lax904597.Problems

open FirstOrder

open FirstOrder.Language Structure

section Digits

/-- The number of a tuple of digits, little-endian in base `c`. -/
def tupleIdx (c : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + c * tupleIdx c l

end Digits

/-- A **finitely presented relational vocabulary**: the relation symbols of `L`
numbered by `Fin numSyms`, with their arities. Reading a symbol off its number
(`sym`) and numbering a symbol (`index`) are mutually inverse, so the
presentation loses nothing.

Every vocabulary of the catalog is of this shape: `Language.turing` has 12
symbols of arity at most 2, `Language.finsat` 14 of arity at most 3. The
presentations are closed under `Language.sum`
(`FirstOrder.Language.FinVocab.sum`), which is what lets the second-order
machinery – whose vocabularies are sums of the instance's with a block's – be
encoded by the same means. -/
structure FinVocab (L : Language.{0, 0}) where
  /-- The number of relation symbols. -/
  numSyms : ℕ
  /-- The symbol with a given number, together with its arity. -/
  symOf : Fin numSyms → ((n : ℕ) × L.Relations n)
  /-- The number of a symbol. -/
  index : ∀ {n : ℕ}, L.Relations n → Fin numSyms
  /-- Reading back the symbol with the number of a symbol gives it back. -/
  symOf_index : ∀ {n : ℕ} (R : L.Relations n), symOf (index R) = ⟨n, R⟩
  /-- Numbering the symbol with a given number gives that number back. -/
  index_symOf : ∀ i : Fin numSyms, index (symOf i).2 = i

namespace FinVocab

variable {L : Language.{0, 0}} (V : FinVocab L)

end FinVocab

/-- A **concrete finite structure** over the finitely presented vocabulary
`V`: a universe size and a table of Booleans, one row per relation symbol.

The universe is `Fin (univSize + 1)`, so it is nonempty by construction; the
row of an `n`-ary symbol is read at the number of the tuple, little-endian in
base `card`. Anything out of range reads `false`, so every pair of a number
and a list of lists of Booleans denotes a structure. -/
structure FinStruct {L : Language.{0, 0}} (V : FinVocab L) where
  /-- One less than the size of the universe. -/
  univSize : ℕ
  /-- The tables of the relations, one row per symbol. -/
  table : List (List Bool)

namespace FinStruct

variable {L : Language.{0, 0}} {V : FinVocab L}

/-- The size of the universe of a concrete finite structure. -/
abbrev card (s : FinStruct V) : ℕ := s.univSize + 1

/-- The universe of a concrete finite structure: nonempty and linearly ordered
by construction. -/
abbrev Univ (s : FinStruct V) : Type := Fin s.card

/-- The table lookup: does the relation `R` hold of the tuple `x`? -/
def relMapBool (s : FinStruct V) {n : ℕ} (R : L.Relations n) (x : Fin n → s.Univ) : Bool :=
  (s.table.getD (V.index R) []).getD (tupleIdx s.card (List.ofFn fun j => (x j : ℕ))) false

end FinStruct

open FirstOrder Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

open FirstOrder

open FirstOrder.Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

end FinVocab

open Lax904597.Machines Lax624099.FiniteSatisfiability Lax624099.CodeHalting

end Lax624099.ConcreteInstances
end
