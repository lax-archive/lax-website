-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Set.Basic

-- Lax314295.KTypes
section
namespace Lax314295.KTypes.tp
end Lax314295.KTypes.tp

namespace Lax314295.KTypes

/-- The type of `k`-types over the alphabet `A`. -/
def TpType (A : Type) : ℕ → Type
  | 0 => Unit
  | k + 1 => Set (TpType A k × A × TpType A k)

end Lax314295.KTypes
end
