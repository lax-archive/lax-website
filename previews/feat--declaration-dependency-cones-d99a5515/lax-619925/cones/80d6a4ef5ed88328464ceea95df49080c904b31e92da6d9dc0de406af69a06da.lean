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

/-- The class of Hadamard-finite series is an effective prevariety over a finite
    alphabet (paper §5, theorem): there is an effective prevariety whose image is
    exactly the Hadamard-finite series, with presentations given by Hadamard
    automata. -/
axiom HadamardEffectivePrevariety (α : Type*) [Fintype α] :
  ∃ P : EffectivePrevariety α, ∀ f, IsHadamardFinite α f ↔ ∃ r : P.Rep, P.sem r = f

end Lax619925.Hadamard
end
