-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Set.Finite.Basic

-- Lax132576.LabelledAutomata
section
namespace Lax132576.LabelledAutomata.LabAut.Path
end Lax132576.LabelledAutomata.LabAut.Path

namespace Lax132576.LabelledAutomata

/-- An automaton whose finitely many transitions are labelled by an input string and
a label from `L`, with distinguished sets of initial and final states. -/
structure LabAut (A L Q : Type) where
  /-- The set of initial states. -/
  init : Set Q
  /-- The set of final states. -/
  final : Set Q
  /-- The transition relation. -/
  δ : Set (Q × List A × L × Q)
  /-- There are only finitely many transitions. -/
  δ_finite : δ.Finite

namespace LabAut

variable {A L Q : Type}

end LabAut

end Lax132576.LabelledAutomata
end

-- Lax132576.RationalRelations
section
namespace Lax132576.RationalRelations
end Lax132576.RationalRelations

namespace Lax132576.RationalRelations.NFAO
end Lax132576.RationalRelations.NFAO
end

-- Lax132576.EpsilonFreeAutomata
section
namespace Lax132576.EpsilonFreeAutomata

open Lax132576.LabelledAutomata

/-- An automaton with extended transitions: transitions are labelled by an input
string and a regular language of output strings. -/
def IsExtendedNFAO {A B Q : Type} (M : LabAut A (Language B) Q) : Prop :=
  ∀ t ∈ M.δ, Language.IsRegular t.2.2.1

end Lax132576.EpsilonFreeAutomata
end
