-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax765601.Aperiodicity
section
namespace Lax765601.Aperiodicity

/-- The `n`-fold concatenation `vⁿ` of a string with itself. -/
def npow {A : Type} (v : List A) : ℕ → List A
  | 0 => []
  | n + 1 => v ++ npow v n

/-- A string-to-string function is aperiodic if for all input strings `u, v, w` the
last letter of `f (u vⁿ w)` — as an element of `Option B`, so that "no letter" is
an admissible value — is the same for all sufficiently large `n`. -/
def Aperiodic {A B : Type} (f : List A → List B) : Prop :=
  ∀ u v w : List A, ∃ o : Option B, ∃ N : ℕ, ∀ n ≥ N, (f (u ++ npow v n ++ w)).getLast? = o

end Lax765601.Aperiodicity
end
