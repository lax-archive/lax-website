-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder

-- Lax392996.SemiringsWithMonus
section
namespace Lax392996
end Lax392996

namespace Lax392996.SemiringsWithMonus
end Lax392996.SemiringsWithMonus

namespace Lax392996.SemiringsWithMonus.HasAltLinearOrder
end Lax392996.SemiringsWithMonus.HasAltLinearOrder

namespace Lax392996.SemiringsWithMonus.SemiringWithMonus
end Lax392996.SemiringsWithMonus.SemiringWithMonus
end

-- Lax392996.BooleanFunctions
section
namespace Lax392996.BooleanFunctions

open Lax392996.SemiringsWithMonus

variable {X : Type}

/-- The type of Boolean functions over Boolean assignments to `X`:
`(X → Bool) → Bool` with pointwise operations. -/
def BoolFunc (X : Type) := (X → Bool) → Bool

instance instOneBoolFunc : One  (BoolFunc X) := ⟨λ _ ↦ True⟩

end Lax392996.BooleanFunctions
end
