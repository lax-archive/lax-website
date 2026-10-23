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

/-- The right derivative with respect to the letter `a`:
    `(rightDeriv a f) w = f (w ++ [a])`, i.e. the coefficient of `w · a` in `f`. -/
def rightDeriv (α : Type*) (a : α) (f : Series α) : Series α := fun w => f (w ++ [a])

end Lax619925.Series
end

-- Lax619925.Prevariety
section
universe u

namespace Lax619925.Prevariety

open Lax619925.Series

set_option linter.dupNamespace false in
/-- A prevariety of series over `α`: a `ℚ`-subspace of `Series α` (the field
    `carrier`) that is closed under the left and right derivatives. -/
structure Prevariety (α : Type*) where
  carrier : Submodule ℚ (Series α)
  closedLeftDeriv : ∀ {f : Series α} (_hf : f ∈ carrier), ∀ a, leftDeriv α a f ∈ carrier
  closedRightDeriv : ∀ {f : Series α} (_hf : f ∈ carrier), ∀ a, rightDeriv α a f ∈ carrier

/-- Membership in a prevariety: `f ∈ P` means that `f` belongs to the underlying
    `ℚ`-subspace of `P`. -/
instance (α : Type*) : Membership (Series α) (Prevariety α) where
  mem P f := f ∈ P.carrier

/-- An effective prevariety of series over `α`: a prevariety given by a type `Rep`
    of finite presentations with a semantics map `sem`, in which the vector-space
    operations and the left and right derivatives are computed by operations on
    presentations (the `sem_*` fields record their correctness), and on which the
    equality problem is decidable.  The fields `prevariety` and `mem` record that
    the image of the semantics is a prevariety. -/
structure EffectivePrevariety (α : Type u) where
  Rep : Type u
  sem : Rep → Series α
  prevariety : Prevariety α
  mem : ∀ r, sem r ∈ prevariety
  zero : Rep
  add : Rep → Rep → Rep
  smul : ℚ → Rep → Rep
  derivL : α → Rep → Rep
  derivR : α → Rep → Rep
  sem_zero : sem zero = 0
  sem_add : ∀ r s, sem (add r s) = sem r + sem s
  sem_smul : ∀ c r, sem (smul c r) = c • sem r
  sem_derivL : ∀ a r, sem (derivL a r) = leftDeriv α a (sem r)
  sem_derivR : ∀ a r, sem (derivR a r) = rightDeriv α a (sem r)
  decEq : ∀ r s, Decidable (sem r = sem s)

end Lax619925.Prevariety
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

/-- A series is *infiltration-finite* (working definition, paper §7) if it belongs to a
    finitely generated differential infiltration algebra: it is an infiltration polynomial
    in a finite tuple of series `fs` that is closed under left derivatives, i.e.
    `f = infiltrationEval k fs p` for some polynomial `p`, and `leftDeriv a (fs i)` is
    again an infiltration polynomial in `fs` for every letter `a` and index `i`.  Here
    `infiltrationEval k fs` is the evaluation in the infiltration algebra generated by
    `fs`. -/
def IsInfiltrationFinite (α : Type*) (f : Series α) : Prop :=
  ∃ k : ℕ, ∃ fs : Fin k → Series α, ∃ p : MvPolynomial (Fin k) ℚ,
    f = infiltrationEval α k fs p ∧
    ∀ a : α, ∀ i : Fin k, ∃ q : MvPolynomial (Fin k) ℚ,
      leftDeriv α a (fs i) = infiltrationEval α k fs q

/-- The class of infiltration-finite series is an effective prevariety over a finite
    alphabet (paper §7, theorem): there is an effective prevariety whose image is
    exactly the infiltration-finite series, with presentations given by infiltration
    automata. -/
axiom InfiltrationEffectivePrevariety (α : Type*) [Fintype α] :
  ∃ P : EffectivePrevariety α, ∀ f, IsInfiltrationFinite α f ↔ ∃ r : P.Rep, P.sem r = f

end Lax619925.Infiltration
end
