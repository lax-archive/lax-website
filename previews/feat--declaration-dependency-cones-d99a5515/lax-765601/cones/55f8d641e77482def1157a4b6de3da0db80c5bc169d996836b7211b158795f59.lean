-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA

-- Lax765601.Continuity
section
namespace Lax765601.Continuity

/-- A relation `R ⊆ A* × B*` is continuous if, for every regular language `L` over
the output alphabet, the set of input strings related to some string of `L` is
regular. -/
def RelContinuous {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∀ L : Language B, L.IsRegular →
    Language.IsRegular ({w : List A | ∃ v, R w v ∧ v ∈ L} : Language A)

end Lax765601.Continuity
end
