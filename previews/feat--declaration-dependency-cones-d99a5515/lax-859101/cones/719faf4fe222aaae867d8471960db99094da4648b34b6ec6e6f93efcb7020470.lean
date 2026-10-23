-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
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
namespace Lax904597.Interpretations.FOReduction
end Lax904597.Interpretations.FOReduction

namespace Lax904597.Interpretations.OrderedFOReduction
end Lax904597.Interpretations.OrderedFOReduction

namespace Lax904597.Interpretations

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A tagged `dim`-dimensional first-order interpretation of `L'` in `L`:
the defining `L`-formula of each relation symbol of `L'`, for each tuple of
tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
argument tuple. -/
structure FOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) where
  /-- The defining `L`-formula of each relation symbol of `L'`, for each tuple
  of tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
  argument tuple. -/
  relFormula : ∀ {n : ℕ}, L'.Relations n → (Fin n → Tag) → L.Formula (Fin n × Fin dim)

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

end FOInterpretation

section Ordered

variable (L : Language.{0, 0}) (A : Type) [L.Structure A] [LE A]

end Ordered

end Lax904597.Interpretations
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

-- Lax366625.WitnessCounting
section
namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting
end

-- Lax859101.SubtractiveReductions
section
namespace Lax859101.SubtractiveReductions.StrongSubtractiveReduction
end Lax859101.SubtractiveReductions.StrongSubtractiveReduction

namespace Lax859101.SubtractiveReductions.SubtractiveReducible
end Lax859101.SubtractiveReductions.SubtractiveReducible

namespace Lax859101.SubtractiveReductions

open Lax366625.CountingProblems Lax366625.WitnessCounting Lax904597.Interpretations

open Lax904597.SecondOrder

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

open FirstOrder

open Language Structure BoundedFormula

section LexFormulas

variable {L : Language.{0, 0}}

/-- `x = y`, as a formula over the ordered expansion. -/
def oEqF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  Term.equal (Term.var x) (Term.var y)

/-- `x ≤ y`, as a formula over the ordered expansion. -/
def oLeF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  Relations.formula₂ leSymb (Term.var x) (Term.var y)

/-- `x < y`, as a formula over the ordered expansion. -/
def oLtF {α : Type} (x y : α) : (L.sum Language.order).Formula α :=
  oLeF x y ⊓ ∼(oEqF x y)

variable {A : Type} [L.Structure A] [LinearOrder A] {α : Type} {v : α → A}

variable (L) in
/-- Lexicographic comparison of two `d`-tuples (the two arguments of a binary
relation), as a formula over the ordered expansion. -/
noncomputable def lexTupleLeF (d : ℕ) : (L.sum Language.order).Formula (Fin 2 × Fin d) :=
  (Formula.iInf fun i : Fin d => oEqF (0, i) (1, i)) ⊔
    Formula.iSup fun j : Fin d =>
      (Formula.iInf fun i : {i : Fin d // i < j} => oEqF (0, i.1) (1, i.1)) ⊓
        oLtF (0, j) (1, j)

open Classical in
variable (L) in
/-- The full lexicographic comparison of tagged tuples, as a formula over the
ordered expansion: the tags are compared statically. -/
noncomputable def lexLeF {Tag : Type} [LinearOrder Tag] (d : ℕ) (t₁ t₂ : Tag) :
    (L.sum Language.order).Formula (Fin 2 × Fin d) :=
  if t₁ = t₂ then lexTupleLeF L d else if t₁ < t₂ then ⊤ else ⊥

end LexFormulas

section OrdExtend

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational]

variable {T : Type} [LinearOrder T] {d : ℕ}

/-- Extension of an interpretation over an ordered base to one whose target
carries the order vocabulary, interpreted by the lexicographic order on
tagged tuples. -/
noncomputable def FOInterpretation.ordExtend
    (I : FOInterpretation (L₁.sum Language.order) L₂ T d) :
    FOInterpretation (L₁.sum Language.order) (L₂.sum Language.order) T d where
  relFormula {n} R :=
    match n, R with
    | _, Sum.inl r => I.relFormula r
    | _, Sum.inr .le => fun t => lexLeF L₁ d (t 0) (t 1)

end OrdExtend

section WitAt

variable [L'.IsRelational] {Tag : Type} [LinearOrder Tag] {dim : ℕ}

end WitAt

open Lax366625.CountingProblems Lax366625.CountingClasses

end Lax859101.SubtractiveReductions
end
