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

/-- The Parikh image (commutative image) of a word: the function counting, for each
    letter, its number of occurrences in the word.  The paper indexes this vector by a
    fixed ordering of the alphabet; the function form is equivalent and needs no order.
    Counting occurrences requires decidable equality on the alphabet. -/
def parikh (α : Type*) [DecidableEq α] (w : List α) : α → ℕ := fun a => w.count a

end Lax619925.Series
end
