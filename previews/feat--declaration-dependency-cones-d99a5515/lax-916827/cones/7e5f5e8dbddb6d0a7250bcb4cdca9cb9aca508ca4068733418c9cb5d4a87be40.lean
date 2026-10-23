-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA

-- Lax765601.Continuity
section
namespace Lax765601.Continuity

/-- A string-to-string function is *continuous* if the inverse image of every
regular language over the output alphabet is a regular language. -/
def Continuous {A B : Type} (f : List A → List B) : Prop :=
  ∀ L : Language B, L.IsRegular → Language.IsRegular ({w : List A | f w ∈ L} : Language A)

end Lax765601.Continuity
end

-- Lax916827.DuplicationContinuous
section
namespace Lax916827.DuplicationContinuous

open Lax765601.Continuity

/-- String duplication is continuous. -/
axiom continuous_duplicate {A : Type} [Finite A] : Continuous (fun w : List A => w ++ w)

end Lax916827.DuplicationContinuous
end
