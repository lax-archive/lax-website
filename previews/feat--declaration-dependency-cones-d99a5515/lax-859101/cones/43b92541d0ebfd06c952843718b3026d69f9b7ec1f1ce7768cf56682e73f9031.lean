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
namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

instance instCoeFun : CoeFun (DecisionProblem L) fun _ => ∀ (A : Type) [L.Structure A], Prop :=
  ⟨Holds⟩

end DecisionProblem

end Lax904597.Problems
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

/-- The universe of the structure interpreted in `A`: tagged `dim`-tuples. -/
protected def Map (_I : FOInterpretation L L' Tag dim) (A : Type) : Type :=
  Tag × (Fin dim → A)

variable (I : FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The `L'`-structure interpreted in the `L`-structure `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2

end FOInterpretation

section Ordered

variable (L : Language.{0, 0}) (A : Type) [L.Structure A] [LE A]

/-- A linearly ordered `L`-structure is a structure over the ordered expansion
`L.sum Language.order`, interpreting the order symbol as `≤`. -/
instance sumOrderStructure : (L.sum Language.order).Structure A :=
  letI := orderStructure (M := A)
  inferInstance

instance sumOrderOrderedStructure : (L.sum Language.order).OrderedStructure A :=
  ⟨fun _ => Iff.rfl⟩

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

/-- The `L'`-structure interpreted on the definable subset. -/
instance mapRelStructure [L'.IsRelational] : L'.Structure (I.MapRel A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1.1).Realize fun p => (xs p.1).1.2 p.2

end RelFOInterpretation

end Lax904597.Relativized
end

-- Lax366625.CountingProblems
section
namespace Lax366625.CountingProblems.OrderedParsimoniousReduction
end Lax366625.CountingProblems.OrderedParsimoniousReduction

namespace Lax366625.CountingProblems.ParsimoniousReduction
end Lax366625.CountingProblems.ParsimoniousReduction

namespace Lax366625.CountingProblems.RelOrderedParsimoniousReduction
end Lax366625.CountingProblems.RelOrderedParsimoniousReduction

namespace Lax366625.CountingProblems.CountingProblem.ofFun
end Lax366625.CountingProblems.CountingProblem.ofFun

namespace Lax366625.CountingProblems

open Lax904597.Interpretations Lax904597.Problems Lax904597.Relativized

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

/-- A counting problem: an isomorphism-invariant natural number attached to
every `L`-structure. Only the values on finite structures are ever read. -/
structure CountingProblem [L.IsRelational] where
  /-- The count: `C A` (through the function coercion) is the number attached
  to the structure `A`. -/
  Count : ∀ (A : Type) [L.Structure A], ℕ
  /-- Counting problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → Count A = Count B

namespace CountingProblem

variable {L} [L.IsRelational]

instance instCoeFun : CoeFun (CountingProblem L) fun _ => ∀ (A : Type) [L.Structure A], ℕ :=
  ⟨Count⟩

end CountingProblem

variable {L} {L' : Language.{0, 0}}

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

end Lax366625.CountingProblems
end

-- Lax366625.CountingClasses
section
namespace Lax366625.CountingClasses

open FirstOrder FirstOrder.Language

open Lax904597.Problems Lax366625.CountingProblems

/-- A counting class: a membership predicate and a hardness predicate on
counting problems, over arbitrary relational vocabularies. -/
structure CountingClass where
  /-- The counting problems belonging to the class. -/
  Mem : ∀ {L : Language.{0, 0}} [L.IsRelational], CountingProblem L → Prop
  /-- The counting problems every problem of the class reduces to. -/
  ParsimoniousHard : ∀ {L : Language.{0, 0}} [L.IsRelational], CountingProblem L → Prop

end Lax366625.CountingClasses
end

-- Lax859101.OneCallReductions
section
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

/-- A one-call counting reduction: a relativized ordered interpretation and a
post-processing term recovering the count of the source from the count of the
interpreted instance. -/
structure OneCallReduction [L.IsRelational] [L'.IsRelational]
    (C : CountingProblem L) (D : CountingProblem L') where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying relativized interpretation, over the ordered expansion. -/
  toRelInterpretation : RelFOInterpretation (L.sum Language.order) L' Tag dim
  /-- The definable domain is inhabited. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (w : Fin dim → A), (toRelInterpretation.domFormula t).Realize w
  /-- The arithmetic applied to the answer of the oracle. -/
  post : PostTerm L
  /-- The count of the source is the post-processed count of the interpreted
  instance, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = post.eval A (D (toRelInterpretation.MapRel A))

open Lax366625.CountingProblems Lax366625.CountingClasses

/-- A counting problem is **one-call hard** for a class when every problem of the
class reduces to it with one call. -/
def OneCallHard (K : CountingClass) {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) :
    Prop :=
  ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''),
    K.Mem D → Nonempty (OneCallReduction D C)

end Lax859101.OneCallReductions
end
