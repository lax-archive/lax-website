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

/-- A linearly ordered `L`-structure is a structure over the ordered expansion
`L.sum Language.order`, interpreting the order symbol as `≤`. -/
instance sumOrderStructure : (L.sum Language.order).Structure A :=
  letI := orderStructure (M := A)
  inferInstance

end Ordered

end Lax904597.Interpretations
end

-- Lax904597.Relativized
section
namespace Lax904597.Relativized.RelOrderedFOReduction
end Lax904597.Relativized.RelOrderedFOReduction

namespace Lax904597.Relativized

open FirstOrder FirstOrder.Language Lax904597.Problems Lax904597.Interpretations

/-- A relativized interpretation: an interpretation together with the domain
formula of each tag. -/
structure RelFOInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ)
    extends FOInterpretation L L' Tag dim where
  /-- The domain formula of each tag: a tagged tuple `(t, ā)` belongs to the
  target universe iff `domFormula t` holds of `ā`. -/
  domFormula : Tag → L.Formula (Fin dim)

namespace RelFOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : RelFOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The universe of the relativized interpretation in `A`: the tagged tuples
whose coordinates satisfy their tag's domain formula. -/
protected def MapRel : Type :=
  {x : Tag × (Fin dim → A) // (I.domFormula x.1).Realize x.2}

end RelFOInterpretation

end Lax904597.Relativized
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

-- Lax859101.OneCallReductions
section
namespace Lax859101.OneCallReductions.OneCallReduction
end Lax859101.OneCallReductions.OneCallReduction

namespace Lax859101.OneCallReductions

open Lax366625.CountingProblems Lax904597.Relativized

open FirstOrder

open Language Structure

/-- Terms denoting numbers polynomial in the size of the instance: numerals,
definable cardinalities, sums and products. -/
inductive PolyTerm (L : Language.{0, 0}) : Type 1
  /-- A numeral. -/
  | num (k : ℕ) : PolyTerm L
  /-- The number of tagged tuples satisfying their tag's domain formula, i.e.,
  the size of the universe of a relativized interpretation. -/
  | card {Tag : Type} [Finite Tag] {dim : ℕ}
      (J : RelFOInterpretation (L.sum Language.order) Language.empty Tag dim) : PolyTerm L
  /-- A sum. -/
  | add (p q : PolyTerm L) : PolyTerm L
  /-- A product. -/
  | mul (p q : PolyTerm L) : PolyTerm L

namespace PolyTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The value of a polynomial term at an ordered structure. -/
noncomputable def eval (A : Type) [L.Structure A] [LinearOrder A] : PolyTerm L → ℕ
  | num k => k
  | card J => Nat.card (J.MapRel A)
  | add p q => p.eval A + q.eval A
  | mul p q => p.eval A * q.eval A

end PolyTerm

/-- The arithmetic applied to the answer of an oracle call: polynomial terms,
powers of two with a polynomial exponent, and the operations `+`, `*`,
truncated `-`, `/` and `%` of the natural numbers. -/
inductive PostTerm (L : Language.{0, 0}) : Type 1
  /-- The answer of the oracle. -/
  | oracle : PostTerm L
  /-- A polynomial term. -/
  | poly (p : PolyTerm L) : PostTerm L
  /-- Two to the power of a polynomial term. -/
  | pow2 (p : PolyTerm L) : PostTerm L
  /-- A sum. -/
  | add (s t : PostTerm L) : PostTerm L
  /-- A product. -/
  | mul (s t : PostTerm L) : PostTerm L
  /-- A truncated difference. -/
  | sub (s t : PostTerm L) : PostTerm L
  /-- A quotient. -/
  | div (s t : PostTerm L) : PostTerm L
  /-- A remainder. -/
  | mod (s t : PostTerm L) : PostTerm L

namespace PostTerm

variable {L L₁ L₂ : Language.{0, 0}}

/-- The value of a post-processing term at an ordered structure, given the
answer `c` of the oracle. -/
noncomputable def eval (A : Type) [L.Structure A] [LinearOrder A] (c : ℕ) : PostTerm L → ℕ
  | oracle => c
  | poly p => p.eval A
  | pow2 p => 2 ^ p.eval A
  | add s t => s.eval A c + t.eval A c
  | mul s t => s.eval A c * t.eval A c
  | sub s t => s.eval A c - t.eval A c
  | div s t => s.eval A c / t.eval A c
  | mod s t => s.eval A c % t.eval A c

end PostTerm

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

open Lax366625.CountingProblems Lax366625.CountingClasses

end Lax859101.OneCallReductions
end
