-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fin.Basic
import Mathlib.Order.Basic

-- Lax14.OrderTypes
section
namespace Lax14.OrderTypes

/-- The order type of a tuple: the relation holding of coordinates `i` and
`j` when the `i`-th entry is strictly smaller than the `j`-th. Two tuples
have the same order type when this relation is the same. -/
def orderType {V : Type*} [LinearOrder V] {ℓ : ℕ} (a : Fin ℓ → V) :
    Fin ℓ → Fin ℓ → Prop :=
  fun i j => a i < a j

end Lax14.OrderTypes
end
