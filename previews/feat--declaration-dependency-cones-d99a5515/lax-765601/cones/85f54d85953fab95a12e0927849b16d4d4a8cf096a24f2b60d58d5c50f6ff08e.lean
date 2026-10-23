-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Infix

-- Lax765601.ElementaryProperties
section
namespace Lax765601.ElementaryProperties

/-- `f` is prefix preserving: `w ⊑ v` implies `f w ⊑ f v`. -/
def PrefixPreserving {A B : Type} (f : List A → List B) : Prop :=
  ∀ w v : List A, w <+: v → f w <+: f v

end Lax765601.ElementaryProperties
end
