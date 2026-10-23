-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax765601.Derivatives
section
namespace Lax765601.Derivatives

/-- The derivative `f(w_)` of `f`: the output `f` produces after having read `w`,
namely `v ↦ f (w v)` with the first `|w|` letters of the output removed. -/
def deriv {A B : Type} (f : List A → List B) (w : List A) : List A → List B :=
  fun v => (f (w ++ v)).drop w.length

end Lax765601.Derivatives
end
