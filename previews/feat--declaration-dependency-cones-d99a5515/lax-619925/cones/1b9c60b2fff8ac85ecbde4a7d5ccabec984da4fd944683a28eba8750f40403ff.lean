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

-- Lax619925.Recognisable
section
namespace Lax619925.Recognisable

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity

/-- A linear representation over `α`: a dimension `k`, a row vector `init` of
    initial weights, a column vector `final` of final weights, and a transition
    function `M` assigning to each letter a `k × k` matrix.  The transition function
    extends homomorphically to words by `M(ε) = 1` and `M(a·w) = M(a) · M(w)` (the
    definition `Mword`), and the series recognised is `f (w) = x · M(w) · y` (the
    definition `sem`).  Both are computed from the four core fields. -/
structure LinearRepresentation (α : Type*) where
  dim : ℕ
  init : Fin dim → ℚ
  final : Fin dim → ℚ
  M : α → Matrix (Fin dim) (Fin dim) ℚ

/-- The word product `M(w)`: `M(ε) = 1` and `M(a·w) = M(a) · M(w)`, the transition
    matrices composed right-to-left along the word. -/
def LinearRepresentation.Mword {α : Type*} (r : LinearRepresentation α) (w : List α) :
    Matrix (Fin r.dim) (Fin r.dim) ℚ :=
  w.foldr (fun a A => r.M a * A) 1

/-- The series recognised by the representation: `f (w) = x · M(w) · y`, the dot
    product of the initial vector with the word product applied to the final vector. -/
def LinearRepresentation.sem {α : Type*} (r : LinearRepresentation α) (w : List α) : ℚ :=
  dotProduct r.init (Matrix.mulVec (r.Mword w) r.final)

/-- A series is *recognisable* if it is recognised by some linear representation. -/
def IsRecognisable (α : Type*) (f : Series α) : Prop :=
  ∃ r : LinearRepresentation α, r.sem = f

/-- The class of recognisable (= linearly finite) series is an effective prevariety
    (paper §4, theorem): there is an effective prevariety whose image is exactly the
    recognisable series, with presentations given by linear representations. -/
axiom RecognisableEffectivePrevariety (α : Type*) [Fintype α] :
  ∃ P : EffectivePrevariety α, ∀ f, IsRecognisable α f ↔ ∃ r : P.Rep, P.sem r = f

end Lax619925.Recognisable
end
