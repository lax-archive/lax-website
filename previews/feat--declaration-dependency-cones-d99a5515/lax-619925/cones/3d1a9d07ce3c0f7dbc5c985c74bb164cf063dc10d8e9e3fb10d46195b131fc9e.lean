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

-- Lax619925.Shuffle
section
namespace Lax619925.Shuffle.ShuffleAutomaton
end Lax619925.Shuffle.ShuffleAutomaton

namespace Lax619925.Shuffle

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity

/-- The recursive core of the shuffle product, defined by primitive recursion on the
    word: `(f ⧢ g) ε = f ε · g ε` and
    `(f ⧢ g) (a·w) = ((leftDeriv a f) ⧢ g) w + (f ⧢ (leftDeriv a g)) w`, the Leibniz
    rule.  This is the unique series satisfying the characterisation.  The recursion
    measure is the word length (the series arguments `f`, `g` change at each step, so
    structural recursion on the word alone does not apply). -/
noncomputable def shuffleRec (α : Type*) (f g : Series α) (w : List α) : ℚ :=
  match w with
  | [] => f [] * g []
  | a :: w' => shuffleRec α (leftDeriv α a f) g w' + shuffleRec α f (leftDeriv α a g) w'
  termination_by w.length

/-- The shuffle product of two series, characterised by the Leibniz rule
    `leftDeriv a (f ⧢ g) = (leftDeriv a f) ⧢ g + f ⧢ (leftDeriv a g)` and the
    initial condition `(f ⧢ g) ε = f ε · g ε`.  Equivalently,
    `(f ⧢ g) w = Σ_{u·v = w} f u · g v`, the sum over all interleavings of `u`
    and `v` that yield `w`. -/
noncomputable def shuffle (α : Type*) (f g : Series α) : Series α :=
  fun w => shuffleRec α f g w

/-- The unit of the shuffle product: the delta series, `1` on the empty word and `0`
    elsewhere.  Unlike the constant-`1` series (the unit of the pointwise product), the
    delta series is the unit of the *shuffle* product. -/
def shuffleUnit (α : Type*) : Series α := fun w => if w = [] then 1 else 0

/-- The `n`-fold iterated shuffle power of `f`: `shufflePow α f 0 = shuffleUnit α` (the
    shuffle unit) and `shufflePow α f (n+1) = f ⧢ shufflePow α f n`.  This is the shuffle
    analogue of the pointwise power `f ^ n` used in `hadamardEval`. -/
noncomputable def shufflePow (α : Type*) (f : Series α) (n : ℕ) : Series α :=
  match n with
  | 0 => shuffleUnit α
  | n + 1 => shuffle α f (shufflePow α f n)

/-- The shuffle product of the iterated shuffle powers `fs 0 ⧢^[d 0] ⧢ ⋯ ⧢ fs (k-1) ⧢^[d (k-1)]`,
    where `⧢` is the shuffle product and `⧢^[n]` is the iterated shuffle power
    (`shufflePow`).  This is the shuffle analogue of the pointwise monomial product
    `∏ i, (fs i) ^ (d i)` used in `hadamardEval`; it is the shuffle fold of the
    commutative-associative shuffle operation over all indices (the zero-exponent terms
    contribute the shuffle unit, which is the identity).  It is computed as a right-fold
    over the index list, so that the definition does not depend on the `Std.Commutative`/
    `Std.Associative` instances (which the axiom-free concept package cannot carry); the
    proof package shows it equals the corresponding `Finset.fold` (`shuffleProd_eq_fold`). -/
noncomputable def shuffleProd (α : Type*) (k : ℕ) (fs : Fin k → Series α) (d : Fin k →₀ ℕ) : Series α :=
  (((Finset.univ : Finset (Fin k)).toList).map (fun i => shufflePow α (fs i) (d i))).foldr
    (fun x acc => shuffle α x acc) (shuffleUnit α)

/-- The evaluation of the polynomial `p` in the *shuffle* algebra, sending `X_i` to
    `fs i`: `shuffleEval α k fs p = ∑ d ∈ p.support, p.coeff d · (fs 0 ⧢^[d 0] ⧢ ⋯ ⧢
    fs (k-1) ⧢^[d (k-1)])`, where `⧢` is the shuffle product and `⧢^[n]` is the iterated
    shuffle power.  This is the shuffle analogue of `hadamardEval` (which evaluates in the
    pointwise ring); because the shuffle ring cannot be a `CommRing` instance on `Series α`
    (which already carries the pointwise ring), it is defined directly as the sum over the
    polynomial's support of the coefficients times the shuffle product of the iterated
    powers. -/
noncomputable def shuffleEval (α : Type*) (k : ℕ) (fs : Fin k → Series α)
    (p : MvPolynomial (Fin k) ℚ) : Series α :=
  p.support.sum fun m => p.coeff m • shuffleProd α k fs m

end Lax619925.Shuffle
end
