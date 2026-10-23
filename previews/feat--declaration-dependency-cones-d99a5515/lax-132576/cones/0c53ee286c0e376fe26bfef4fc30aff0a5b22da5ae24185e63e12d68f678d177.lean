-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Halting
import Mathlib.Data.Set.Finite.Basic

-- Lax132576.LabelledAutomata
section
namespace Lax132576
end Lax132576

namespace Lax132576.LabelledAutomata
end Lax132576.LabelledAutomata

namespace Lax132576.LabelledAutomata.LabAut
end Lax132576.LabelledAutomata.LabAut

namespace Lax132576.LabelledAutomata.LabAut.Path
end Lax132576.LabelledAutomata.LabAut.Path
end

-- Lax132576.RationalRelations
section
namespace Lax132576.RationalRelations
end Lax132576.RationalRelations

namespace Lax132576.RationalRelations.NFAO
end Lax132576.RationalRelations.NFAO
end

-- Lax132576.TransducerCodes
section
namespace Lax132576.TransducerCodes.RelCode
end Lax132576.TransducerCodes.RelCode

namespace Lax132576.TransducerCodes

open Lax132576.LabelledAutomata Lax132576.RationalRelations

/-- A property `P` is decidable under a promise if a computable Boolean-valued
function answers `P` correctly on every input satisfying the promise. -/
def DecidableUnderPromise {α : Type} [Primcodable α] (promise P : α → Prop) : Prop :=
  ∃ D : α → Bool, Computable D ∧ ∀ a, promise a → (D a = true ↔ P a)

end Lax132576.TransducerCodes
end
