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

/-- Two words are *commutatively equivalent* if they have the same multiset of letters,
    i.e. one is obtained from the other by permuting the positions of the letters.
    (Equivalently, when the alphabet has decidable equality, they have the same Parikh
    image.) -/
def CommutativelyEquivalent (α : Type*) (u v : List α) : Prop :=
  Multiset.ofList u = Multiset.ofList v

end Lax619925.Series
end
