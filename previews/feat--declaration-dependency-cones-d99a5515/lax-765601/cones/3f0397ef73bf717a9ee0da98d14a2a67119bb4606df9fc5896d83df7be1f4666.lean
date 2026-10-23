-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Infix

-- Lax765601.ElementaryProperties
section
namespace Lax765601.ElementaryProperties

/-- `f` is prefix determined: the first `n` output letters depend only on the
first `n` input letters. -/
def PrefixDetermined {A B : Type} (f : List A → List B) : Prop :=
  ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n

end Lax765601.ElementaryProperties
end
