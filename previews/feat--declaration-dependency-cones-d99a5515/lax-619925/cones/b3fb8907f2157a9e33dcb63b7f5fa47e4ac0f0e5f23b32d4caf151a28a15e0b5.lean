-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span.Basic

-- Lax619925.Series
section
namespace Lax619925.Series

set_option linter.dupNamespace false in
/-- A formal power series over the alphabet `α`: a function from words to `ℚ`. -/
abbrev Series (α : Type*) := List α → ℚ

/-- The left derivative with respect to the letter `a`:
    `(leftDeriv a f) w = f (a :: w)`, i.e. the coefficient of `a · w` in `f`. -/
def leftDeriv (α : Type*) (a : α) (f : Series α) : Series α := fun w => f (a :: w)

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
namespace Lax619925.Commutativity
end Lax619925.Commutativity

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
end

-- Lax619925.Recognisable
section
namespace Lax619925.Recognisable.LinearRepresentation
end Lax619925.Recognisable.LinearRepresentation

namespace Lax619925.Recognisable

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity

/-- A series is *linearly finite* if it belongs to a finitely generated `ℚ`-space of
    series (the span of a finite set of generators `G`) that is closed under left
    derivatives: `f ∈ span G` and `leftDeriv a g ∈ span G` for all `a` and `g ∈ G`. -/
def IsLinearlyFinite (α : Type*) (f : Series α) : Prop :=
  ∃ G : Finset (Series α), f ∈ Submodule.span ℚ G ∧ ∀ a, ∀ g ∈ G, leftDeriv α a g ∈ Submodule.span ℚ G

/-- The class of linearly finite series is closed under scalar product, addition,
    and left derivatives (paper §4, lemma `recognisable closure properties`).  The
    closure is effective: each operation is witnessed by an explicit finite set of
    generators.  These three parts hold over any alphabet. -/
axiom LinearlyFiniteClosure (α : Type*) :
  (∀ (f g : Series α), IsLinearlyFinite α f → IsLinearlyFinite α g → IsLinearlyFinite α (f + g)) ∧
  (∀ (c : ℚ) (f : Series α), IsLinearlyFinite α f → IsLinearlyFinite α (c • f)) ∧
  (∀ (a : α) (f : Series α), IsLinearlyFinite α f → IsLinearlyFinite α (leftDeriv α a f))

end Lax619925.Recognisable
end
