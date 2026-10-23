-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Finite.Defs
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
namespace Lax619925.Prevariety.EffectivePrevariety
end Lax619925.Prevariety.EffectivePrevariety

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

end Lax619925.Prevariety
end
