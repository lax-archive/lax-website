-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib

-- Lax41.MoserTardosDefinitions
section
namespace Lax41.MoserTardosDefinitions.ResamplingRule
end Lax41.MoserTardosDefinitions.ResamplingRule

set_option autoImplicit false

open scoped ENNReal

namespace Lax41.MoserTardosDefinitions

variable {Event : Type} [Fintype Event] [DecidableEq Event]

variable {Variable : Type} [Fintype Variable] [DecidableEq Variable]

variable (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]

/-- A complete assignment to the finite family of independent variables. -/
abbrev Assignment := ∀ i, Value i

end Lax41.MoserTardosDefinitions
end
