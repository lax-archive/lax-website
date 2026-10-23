-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Basic
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

-- Lax619925.Infiltration
section
namespace Lax619925.Infiltration.InfiltrationAutomaton
end Lax619925.Infiltration.InfiltrationAutomaton

namespace Lax619925.Infiltration.infiltrationPow
end Lax619925.Infiltration.infiltrationPow

namespace Lax619925.Infiltration

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity

/-- The recursive core of the infiltration product, defined by primitive recursion on
    the word: `(f ↑ g) ε = f ε · g ε` and
    `(f ↑ g) (a·w) = ((leftDeriv a f) ↑ g) w + (f ↑ (leftDeriv a g)) w
     + ((leftDeriv a f) ↑ (leftDeriv a g)) w`.  The recursion measure is the word
    length (the series arguments change at each step). -/
noncomputable def infiltrationRec (α : Type*) (f g : Series α) (w : List α) : ℚ :=
  match w with
  | [] => f [] * g []
  | a :: w' => infiltrationRec α (leftDeriv α a f) g w'
    + infiltrationRec α f (leftDeriv α a g) w'
    + infiltrationRec α (leftDeriv α a f) (leftDeriv α a g) w'
  termination_by w.length

/-- The infiltration product of two series, characterised by the base case
    `(f ↑ g) ε = f ε · g ε` and the step rule
    `leftDeriv a (f ↑ g) = (leftDeriv a f) ↑ g + f ↑ (leftDeriv a g)
     + (leftDeriv a f) ↑ (leftDeriv a g)`.  It is the synchronising-interleaving
    analogue of the shuffle product (the extra last term allows the two series to
    consume the letter jointly). -/
noncomputable def infiltration (α : Type*) (f g : Series α) : Series α :=
  fun w => infiltrationRec α f g w

end Lax619925.Infiltration
end
