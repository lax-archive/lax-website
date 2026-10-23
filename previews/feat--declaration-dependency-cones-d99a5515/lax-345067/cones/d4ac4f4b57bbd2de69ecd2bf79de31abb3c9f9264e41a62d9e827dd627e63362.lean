-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Basic
import Mathlib.Order.Basic

-- Lax345067.OrderTypes
section
namespace Lax345067.OrderTypes

/-- The order type of a tuple: the relation holding of coordinates `i` and
`j` when the `i`-th entry is strictly smaller than the `j`-th. Two tuples
have the same order type when this relation is the same. -/
def orderType {V : Type*} [LinearOrder V] {ℓ : ℕ} (a : Fin ℓ → V) :
    Fin ℓ → Fin ℓ → Prop :=
  fun i j => a i < a j

end Lax345067.OrderTypes
end
