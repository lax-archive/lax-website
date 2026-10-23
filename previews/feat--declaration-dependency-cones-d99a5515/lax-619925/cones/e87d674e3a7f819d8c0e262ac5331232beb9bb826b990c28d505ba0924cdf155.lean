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

/-- The unit of the infiltration product: the delta series, `1` on the empty word and
    `0` elsewhere.  Unlike the constant-`1` series (the unit of the pointwise product),
    the delta series is the unit of the *infiltration* product. -/
def infiltrationUnit (α : Type*) : Series α := fun w => if w = [] then 1 else 0

/-- The `n`-fold iterated infiltration power of `f`: `infiltrationPow α f 0 =
    infiltrationUnit α` (the infiltration unit) and `infiltrationPow α f (n+1) = f ↑
    infiltrationPow α f n`.  This is the infiltration analogue of the pointwise power
    `f ^ n` used in `hadamardEval`. -/
noncomputable def infiltrationPow (α : Type*) (f : Series α) (n : ℕ) : Series α :=
  match n with
  | 0 => infiltrationUnit α
  | n + 1 => infiltration α f (infiltrationPow α f n)

/-- The infiltration product of the iterated infiltration powers
    `fs 0 ↑^[d 0] ⋯ fs (k-1) ↑^[d (k-1)]`, where `↑` is the infiltration product and
    `↑^[n]` is the iterated infiltration power (`infiltrationPow`).  This is the
    infiltration analogue of the pointwise monomial product `∏ i, (fs i) ^ (d i)` used in
    `hadamardEval`; it is the infiltration fold of the commutative-associative infiltration
    operation over all indices (the zero-exponent terms contribute the infiltration unit,
    which is the identity).  It is computed as a right-fold over the index list, so that
    the definition does not depend on the `Std.Commutative`/`Std.Associative` instances
    (which the axiom-free concept package cannot carry); the proof package shows it equals
    the corresponding `Finset.fold` (`infiltrationProd_eq_fold`). -/
noncomputable def infiltrationProd (α : Type*) (k : ℕ) (fs : Fin k → Series α) (d : Fin k →₀ ℕ) : Series α :=
  (((Finset.univ : Finset (Fin k)).toList).map (fun i => infiltrationPow α (fs i) (d i))).foldr
    (fun x acc => infiltration α x acc) (infiltrationUnit α)

/-- The evaluation of the polynomial `p` in the *infiltration* algebra, sending `X_i` to
    `fs i`: `infiltrationEval α k fs p = ∑ d ∈ p.support, p.coeff d · (fs 0 ↑^[d 0] ⋯
    fs (k-1) ↑^[d (k-1)])`, where `↑` is the infiltration product and `↑^[n]` is the
    iterated infiltration power.  This is the infiltration analogue of `hadamardEval`
    (which evaluates in the pointwise ring); because the infiltration ring cannot be a
    `CommRing` instance on `Series α` (which already carries the pointwise ring), it is
    defined directly as the sum over the polynomial's support of the coefficients times
    the infiltration product of the iterated powers. -/
noncomputable def infiltrationEval (α : Type*) (k : ℕ) (fs : Fin k → Series α)
    (p : MvPolynomial (Fin k) ℚ) : Series α :=
  p.support.sum fun m => p.coeff m • infiltrationProd α k fs m

end Lax619925.Infiltration
end
