-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Basic
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

-- Lax619925.Hadamard
section
namespace Lax619925.Hadamard.HadamardAutomaton
end Lax619925.Hadamard.HadamardAutomaton

namespace Lax619925.Hadamard

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity

/-- The Hadamard-algebra evaluation of the polynomial `p` at the series `fs`:
    `hadamardEval fs p = Σ_m p m · ∏_i (fs i)^{m i}`, the interpretation of `p` in
    the (pointwise) ring of series, where the variable `X_i` is mapped to `fs i` and
    the multiplication is the Hadamard (pointwise) product. -/
def hadamardEval (α : Type*) (k : ℕ) (fs : Fin k → Series α) (p : MvPolynomial (Fin k) ℚ) :
    Series α :=
  fun w => p.support.sum fun m => p.coeff m * ∏ i : Fin k, (fs i) w ^ (m i)

/-- A series is *Hadamard-finite* (working definition, paper §5) if it is a Hadamard
    polynomial in a finite tuple of series `fs` that is closed under left
    derivatives: `f = p(fs)` for some polynomial `p`, and `leftDeriv a (fs i)` is
    again a Hadamard polynomial in `fs` for every letter `a` and index `i`.  Here
    `p(fs)` is the evaluation of `p` in the (pointwise) ring of series, i.e. the
    Hadamard algebra. -/
def IsHadamardFinite (α : Type*) (f : Series α) : Prop :=
  ∃ k : ℕ, ∃ fs : Fin k → Series α, ∃ p : MvPolynomial (Fin k) ℚ,
    f = hadamardEval α k fs p ∧
    ∀ a : α, ∀ i : Fin k, ∃ q : MvPolynomial (Fin k) ℚ,
      leftDeriv α a (fs i) = hadamardEval α k fs q

end Lax619925.Hadamard
end
