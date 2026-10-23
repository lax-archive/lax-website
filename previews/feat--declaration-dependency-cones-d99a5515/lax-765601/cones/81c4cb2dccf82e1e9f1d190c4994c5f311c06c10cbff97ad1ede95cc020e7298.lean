-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Infix

-- Lax765601.ElementaryProperties
section
namespace Lax765601.ElementaryProperties

/-- `f` is length preserving, i.e. letter-to-letter: the output has the length of
the input. -/
def LengthPreserving {A B : Type} (f : List A → List B) : Prop :=
  ∀ w : List A, (f w).length = w.length

end Lax765601.ElementaryProperties
end
