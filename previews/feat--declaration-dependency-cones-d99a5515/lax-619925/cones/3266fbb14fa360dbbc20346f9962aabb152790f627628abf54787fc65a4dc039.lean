-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic

-- Lax619925.Series
section
namespace Lax619925.Series

set_option linter.dupNamespace false in
/-- A formal power series over the alphabet `α`: a function from words to `ℚ`. -/
abbrev Series (α : Type*) := List α → ℚ

/-- The left derivative with respect to the letter `a`:
    `(leftDeriv a f) w = f (a :: w)`, i.e. the coefficient of `a · w` in `f`. -/
def leftDeriv (α : Type*) (a : α) (f : Series α) : Series α := fun w => f (a :: w)

/-- The right derivative with respect to the letter `a`:
    `(rightDeriv a f) w = f (w ++ [a])`, i.e. the coefficient of `w · a` in `f`. -/
def rightDeriv (α : Type*) (a : α) (f : Series α) : Series α := fun w => f (w ++ [a])

/-- Two words are *commutatively equivalent* if they have the same multiset of letters,
    i.e. one is obtained from the other by permuting the positions of the letters.
    (Equivalently, when the alphabet has decidable equality, they have the same Parikh
    image.) -/
def CommutativelyEquivalent (α : Type*) (u v : List α) : Prop :=
  Multiset.ofList u = Multiset.ofList v

/-- A series is *commutative* (échangeable) if it takes the same value on all
    commutatively equivalent words. -/
def IsCommutative (α : Type*) (f : Series α) : Prop :=
  ∀ u v, CommutativelyEquivalent α u v → f u = f v

end Lax619925.Series
end

-- Lax619925.Prevariety
section
namespace Lax619925.Prevariety
end Lax619925.Prevariety

namespace Lax619925.Prevariety.EffectivePrevariety
end Lax619925.Prevariety.EffectivePrevariety

namespace Lax619925.Prevariety.Prevariety
end Lax619925.Prevariety.Prevariety
end

-- Lax619925.Commutativity
section
namespace Lax619925.Commutativity.Fresh2
end Lax619925.Commutativity.Fresh2

namespace Lax619925.Commutativity.antiDerivativeSeries
end Lax619925.Commutativity.antiDerivativeSeries

namespace Lax619925.Commutativity.extendSeries
end Lax619925.Commutativity.extendSeries

namespace Lax619925.Commutativity.liftWordOpt
end Lax619925.Commutativity.liftWordOpt

namespace Lax619925.Commutativity.Fresh2.fresh0
end Lax619925.Commutativity.Fresh2.fresh0

namespace Lax619925.Commutativity.Fresh2.fresh1
end Lax619925.Commutativity.Fresh2.fresh1

namespace Lax619925.Commutativity.Fresh2.letter
end Lax619925.Commutativity.Fresh2.letter

namespace Lax619925.Commutativity

open Lax619925.Series Lax619925.Prevariety

/-- The *swap* equation: for all letters `a, b`,
    `leftDeriv a (leftDeriv b f) = leftDeriv b (leftDeriv a f)`.
    It expresses that exchanging the first two letters of a word does not change
    the coefficient. -/
def SatisfiesSwap (α : Type*) (f : Series α) : Prop :=
  ∀ a b, leftDeriv α a (leftDeriv α b f) = leftDeriv α b (leftDeriv α a f)

/-- The *rotate* equation: for all letters `a`,
    `leftDeriv a f = rightDeriv a f`.
    It expresses that moving the first letter to the end does not change the
    coefficient. -/
def SatisfiesRotate (α : Type*) (f : Series α) : Prop :=
  ∀ a, leftDeriv α a f = rightDeriv α a f

/-- A series is commutative if and only if it satisfies the swap and rotate equations
    for all letters (paper §3, lemma `commutativity`).  Swaps and rotations generate
    all commutatively equivalent words, so the two finite families of equations
    characterise commutativity. -/
axiom FiniteAxiomatisation (α : Type*) (f : Series α) :
  IsCommutative α f ↔ SatisfiesSwap α f ∧ SatisfiesRotate α f

end Lax619925.Commutativity
end
