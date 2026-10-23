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
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
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
namespace Lax485149.SecondOrderAtoms

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- An atom `R i (x_{f 0}, …)` in the relation variables of a block, with
arguments read from `k` universally quantified first-order variables. -/
structure SOAtom (B : SOBlock) (k : ℕ) where
  /-- The relation variable of the block the atom is about. -/
  idx : B.ι
  /-- The arguments, as indices among the `k` universally quantified
  variables. -/
  args : Fin (B.arity idx) → Fin k

variable {B : SOBlock} {k : ℕ}

end Lax485149.SecondOrderAtoms
end

-- Lax535992.HornFragment
section
namespace Lax535992.HornFragment.HornProgram
end Lax535992.HornFragment.HornProgram

namespace Lax535992.HornFragment

open Lax485149.SecondOrderAtoms Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- A Horn clause over the input vocabulary `L` and the block `B`, with `k`
universally quantified first-order variables: an arbitrary first-order guard
over `L` and a list of second-order body atoms imply the head atom – or `⊥`,
when the head is `none` (a *goal* clause). -/
structure HornClause (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) where
  /-- The first-order guard, over the input vocabulary alone. -/
  guard : L.Formula (Fin k)
  /-- The body: second-order atoms, all of them positive. -/
  body : List (SOAtom B k)
  /-- The head: a second-order atom, or `none` for a goal clause. -/
  head : Option (SOAtom B k)

section Semantics

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ} {A : Type} [L.Structure A]

end Semantics

end Lax535992.HornFragment
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
namespace Lax366625.QuantitativeLogic.QLFPDef
end Lax366625.QuantitativeLogic.QLFPDef

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

namespace Lax366625.QuantitativeLogic

open Lax366625.CountingProblems Lax535992.HornFragment Lax535992.LeastFixedPoint

open Lax895169.BitPredicate Lax904597.SecondOrder

open FirstOrder

open Language Structure

/-- A definition of a number by its binary digits: a least fixed point, as for
`LFPDef`, and the relation variables holding the
digits. -/
structure DigitLFPDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the fixed point. -/
  B : SOBlock
  /-- The number of first-order variables shared by the rules. -/
  k : ℕ
  /-- The rules defining the variables. -/
  rules : List (HornClause (L.sum Language.order) B k)
  /-- The number of relation variables holding digits. -/
  c : ℕ
  /-- There is at least one. -/
  c_pos : 0 < c
  /-- Their common arity. -/
  ℓ : ℕ
  /-- The relation variables holding the digits, the least significant
  first. -/
  bit : Fin c → B.ι
  /-- They are distinct. -/
  bit_injective : Function.Injective bit
  /-- They have the same arity. -/
  arity_bit : ∀ τ, B.arity (bit τ) = ℓ

namespace DigitLFPDef

variable {L : Language.{0, 0}} (d : DigitLFPDef L) (A : Type) [L.Structure A] [LinearOrder A]

end DigitLFPDef

open FirstOrder

open Language Structure

namespace QTerm

variable {L L' : Language.{0, 0}}

end QTerm

variable {L : Language.{0, 0}} [L.IsRelational]

open Lax366625.CountingClasses

end Lax366625.QuantitativeLogic
end
