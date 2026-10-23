-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Card
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

-- Lax345067.TupleRamsey
section
namespace Lax345067.TupleRamsey

open Lax345067.OrderTypes

/-- Ramsey's theorem for tuples: every `k`-colouring of the `ℓ`-tuples
over a large enough linearly ordered finite set has a subset of size `s`
on which the colour of a tuple depends only on its order type. -/
axiom exists_orderType_homogeneous (k ℓ s : ℕ) :
    ∃ N : ℕ, ∀ (n : ℕ) (c : (Fin ℓ → Fin n) → Fin k), N ≤ n →
      ∃ I : Set (Fin n), s ≤ I.ncard ∧
        ∀ a b : Fin ℓ → Fin n, (∀ i, a i ∈ I) → (∀ i, b i ∈ I) →
          orderType a = orderType b → c a = c b

end Lax345067.TupleRamsey
end
