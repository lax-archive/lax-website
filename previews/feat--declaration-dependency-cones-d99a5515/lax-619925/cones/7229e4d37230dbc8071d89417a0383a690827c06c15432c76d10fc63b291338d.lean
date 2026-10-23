-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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

/-- Left and right derivatives commute: for all letters `a, b`,
    `leftDeriv a ∘ rightDeriv b = rightDeriv b ∘ leftDeriv a`.
    (Paper, §2, lemma `leftRightComm`.)  Both sides send a series `f` to the series
    `w ↦ f (a :: w ++ [b])`. -/
axiom LeftRightDerivativesCommute (α : Type*) (a b : α) :
  leftDeriv α a ∘ rightDeriv α b = rightDeriv α b ∘ leftDeriv α a

end Lax619925.Series
end
