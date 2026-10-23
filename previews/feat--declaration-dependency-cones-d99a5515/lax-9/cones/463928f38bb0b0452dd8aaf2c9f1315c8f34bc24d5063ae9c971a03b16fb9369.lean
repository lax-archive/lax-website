-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax9.MergeWidth
section
namespace Lax9.MergeWidth

open scoped Classical

universe u

variable {V : Type u} [Fintype V]

namespace MergeSeq

variable {G : SimpleGraph V}

end MergeSeq

/-- A **graph class**: a property of finite simple graphs. -/
def GraphClass : Type 1 := ∀ ⦃V : Type⦄ [Fintype V], SimpleGraph V → Prop

end Lax9.MergeWidth
end
