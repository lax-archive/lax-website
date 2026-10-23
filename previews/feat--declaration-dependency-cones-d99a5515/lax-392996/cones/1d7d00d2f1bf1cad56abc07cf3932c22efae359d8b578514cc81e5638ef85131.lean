-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.Defs.LinearOrder

-- Lax392996.SemiringsWithMonus
section
namespace Lax392996.SemiringsWithMonus.SemiringWithMonus
end Lax392996.SemiringsWithMonus.SemiringWithMonus

universe u

namespace Lax392996.SemiringsWithMonus

/-- An alternative linear order on a type, used to order annotations when
they share a column with data values. -/
class HasAltLinearOrder (α : Type u) where
  altOrder : LinearOrder α

end Lax392996.SemiringsWithMonus
end
