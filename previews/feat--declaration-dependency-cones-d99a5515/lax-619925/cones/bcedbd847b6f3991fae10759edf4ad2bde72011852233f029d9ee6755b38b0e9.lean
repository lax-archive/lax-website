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

/-- The reversal of a series: `(reversal f) w = f (w.reverse)`. -/
def reversal (α : Type*) (f : Series α) : Series α := fun w => f w.reverse

/-- Reversal interchanges left and right derivatives:
    `reversal (leftDeriv a f) = rightDeriv a (reversal f)`.
    Composing with the involution gives the paper's double-reversal identity
    `rightDeriv a f = reversal (leftDeriv a (reversal f))` used in §4. -/
axiom ReversalSwapsDerivatives (α : Type*) (a : α) (f : Series α) :
  reversal α (leftDeriv α a f) = rightDeriv α a (reversal α f)

end Lax619925.Series
end
