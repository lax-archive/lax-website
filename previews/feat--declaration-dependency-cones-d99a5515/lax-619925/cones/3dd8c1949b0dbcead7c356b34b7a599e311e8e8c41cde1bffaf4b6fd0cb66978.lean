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

/-- The right derivative with respect to a word `w`, extended homomorphically:
    `(rightDerivWord w f) v = f (v ++ w.reverse)`.  This agrees with the paper's
    recursive definition `δ^R_ε f = f` and `δ^R_{w·a} f = δ^R_a (δ^R_w f)`, which
    appends the letters of `w` in reversed order. -/
def rightDerivWord (α : Type*) (w : List α) (f : Series α) : Series α := fun v => f (v ++ w.reverse)

end Lax619925.Series
end
