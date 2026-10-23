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
namespace Lax624099.FiniteSatisfiability.FinSat.IsWF
end Lax624099.FiniteSatisfiability.FinSat.IsWF

namespace Lax624099.FiniteSatisfiability.FinSat.gval
end Lax624099.FiniteSatisfiability.FinSat.gval

namespace Lax624099.FiniteSatisfiability

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of encoded first-order sentences in
negation normal form. -/
inductive finsatRel : ℕ → Type
  /-- `le x y`: the order of the syntax. -/
  | le : finsatRel 2
  /-- `andN g`: the node `g` is the conjunction of its children. -/
  | andN : finsatRel 1
  /-- `orN g`: the node `g` is the disjunction of its children. -/
  | orN : finsatRel 1
  /-- `allN g`: the node `g` universally quantifies its bound variable. -/
  | allN : finsatRel 1
  /-- `exN g`: the node `g` existentially quantifies its bound variable. -/
  | exN : finsatRel 1
  /-- `child g c`: the node `c` is one of the children of the node `g`. -/
  | child : finsatRel 2
  /-- `bind g x`: the quantifier node `g` binds the variable `x`. -/
  | bind : finsatRel 2
  /-- `eqL g x y`: the node `g` is the literal `x = y`. -/
  | eqL : finsatRel 3
  /-- `neqL g x y`: the node `g` is the literal `x ≠ y`. -/
  | neqL : finsatRel 3
  /-- `posL g s`: the node `g` is a positive atom of the relation symbol
  `s`. -/
  | posL : finsatRel 2
  /-- `negL g s`: the node `g` is a negated atom of the relation symbol
  `s`. -/
  | negL : finsatRel 2
  /-- `arg g p x`: the argument of the atom `g` at position `p` is the
  variable `x`. -/
  | arg : finsatRel 3
  /-- `sig s p`: the relation symbol `s` has an argument position `p`. -/
  | sig : finsatRel 2
  /-- `root g`: the node `g` is the root of the encoded sentence. -/
  | root : finsatRel 1
  deriving DecidableEq

/-- The relational vocabulary of encoded first-order sentences: a parse DAG in
negation normal form, ordered by the order of its own syntax. -/
def finsat : Language :=
  ⟨fun _ => Empty, finsatRel⟩

open FirstOrder

open Language Structure

namespace FinSat

section Reading

variable {A : Type} [finsat.Structure A]

end Reading

section Semantics

variable {A M : Type} [finsat.Structure A]

end Semantics

end FinSat

open Lax904597.Problems Lax624099.Problems

end Lax624099.FiniteSatisfiability
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

namespace Lax624099.ConcreteInstances.tupleIdx
end Lax624099.ConcreteInstances.tupleIdx

namespace Lax624099.ConcreteInstances.FinStruct.equivProd
end Lax624099.ConcreteInstances.FinStruct.equivProd

namespace Lax624099.ConcreteInstances

open Lax904597.Problems

open FirstOrder

open FirstOrder.Language Structure

section Digits

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

namespace FinStruct

variable {L : Language.{0, 0}} {V : FinVocab L}

end FinStruct

open FirstOrder Language Structure

variable {L : Language.{0, 0}} [L.IsRelational]

open FirstOrder

open FirstOrder.Language

namespace FinVocab

variable {L L' : Language.{0, 0}}

end FinVocab

open Lax904597.Machines Lax624099.FiniteSatisfiability Lax624099.CodeHalting

instance instDecidableEqSigmaNatRelationsFinsat : DecidableEq ((n : ℕ) × finsat.Relations n) := by
  show DecidableEq ((n : ℕ) × finsatRel n)
  infer_instance

end Lax624099.ConcreteInstances
end
