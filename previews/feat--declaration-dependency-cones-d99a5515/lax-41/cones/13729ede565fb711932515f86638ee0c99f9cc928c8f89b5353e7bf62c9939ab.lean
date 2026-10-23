-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib

-- Lax41.MoserTardosDefinitions
section
namespace Lax41
end Lax41

namespace Lax41.MoserTardosDefinitions
end Lax41.MoserTardosDefinitions

namespace Lax41.MoserTardosDefinitions.ResamplingRule
end Lax41.MoserTardosDefinitions.ResamplingRule
end

-- Lax41.HaeuplerSahaSrinivasanDefinitions
section
set_option autoImplicit false

open scoped ENNReal

namespace Lax41.HaeuplerSahaSrinivasanDefinitions

open Lax41.MoserTardosDefinitions

variable {Event : Type} [Fintype Event] [DecidableEq Event]

variable {Variable : Type} [Fintype Variable] [DecidableEq Variable]

variable (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]

/-- An event belonging to the finite family on which the algorithm runs. -/
abbrev BadEventIndex (badEvents : Finset Event) := {A // A ∈ badEvents}

end Lax41.HaeuplerSahaSrinivasanDefinitions
end
