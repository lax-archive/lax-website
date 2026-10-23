-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
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

-- Lax392996.WhyProvenance
section
namespace Lax392996.WhyProvenance

open Lax392996.SemiringsWithMonus

variable {α : Type}

/-- Why-provenance over `α`: a family of sets of witnesses. -/
@[ext]
structure Why (α: Type) where
  carrier : Set (Set α)

instance instZeroWhy : Zero (Why α) where
  zero := ⟨∅⟩

/-- Why-provenance: `𝟘` is `∅`. -/
axiom Why.zero_carrier : (0 : Why α).carrier = ∅

end Lax392996.WhyProvenance
end
