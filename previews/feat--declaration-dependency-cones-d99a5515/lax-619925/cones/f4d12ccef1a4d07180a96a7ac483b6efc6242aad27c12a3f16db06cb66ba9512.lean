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

/-- The support of a series: the set of words on which it is nonzero. -/
def support (α : Type*) (f : Series α) : Set (List α) := {w | f w ≠ 0}

/-- A series is a *polynomial* if its support is finite. -/
def IsPolynomial (α : Type*) (f : Series α) : Prop := (support α f).Finite

end Lax619925.Series
end
