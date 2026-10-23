-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Lattice

-- Lax979537.LeastFixedPoints
section
namespace Lax979537.LeastFixedPoints

def stage {α : Type} (F : Set α → Set α) : Nat → Set α
  | 0 => ∅
  | t + 1 => F (stage F t)

end Lax979537.LeastFixedPoints
end
