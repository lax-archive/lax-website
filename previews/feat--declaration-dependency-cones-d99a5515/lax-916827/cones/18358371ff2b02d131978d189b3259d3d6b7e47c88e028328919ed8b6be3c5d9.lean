-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

-- Lax916827.StreamingStringTransducers
section
namespace Lax916827.StreamingStringTransducers.Copyless
end Lax916827.StreamingStringTransducers.Copyless

namespace Lax916827.StreamingStringTransducers

namespace SST

variable {A B Q X : Type} [Fintype X]

/-- Substituting the contents of the registers into a string over `X + B`. -/
def subst (η : X → List B) (s : List (X ⊕ B)) : List B :=
  (s.map (fun z => match z with | Sum.inl x => η x | Sum.inr b => [b])).flatten

end SST

end Lax916827.StreamingStringTransducers
end
