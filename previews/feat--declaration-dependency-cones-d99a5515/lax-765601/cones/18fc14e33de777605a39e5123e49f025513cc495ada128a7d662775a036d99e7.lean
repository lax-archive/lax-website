-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA

-- Lax765601.Continuity
section
namespace Lax765601.Continuity

/-- A partial function is continuous if, for every regular language `L` over the
output alphabet, the set of input strings whose output is defined and belongs to
`L` is regular. -/
def PartialContinuous {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∀ L : Language B, L.IsRegular →
    Language.IsRegular ({w : List A | ∃ v, f w = some v ∧ v ∈ L} : Language A)

end Lax765601.Continuity
end
