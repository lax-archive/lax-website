-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax965890.MoserTardosDefinitions
section
namespace Lax965890.MoserTardosDefinitions.ResamplingRule
end Lax965890.MoserTardosDefinitions.ResamplingRule

set_option autoImplicit false

open scoped ENNReal

namespace Lax965890.MoserTardosDefinitions

variable {Event : Type} [Fintype Event] [DecidableEq Event]

variable {Variable : Type} [Fintype Variable] [DecidableEq Variable]

variable (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]

/-- A complete assignment to the finite family of independent variables. -/
abbrev Assignment := ∀ i, Value i

end Lax965890.MoserTardosDefinitions
end
