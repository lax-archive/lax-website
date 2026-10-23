-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Lattice

-- Lax751879.LeastFixedPoints
section
namespace Lax751879.LeastFixedPoints

def stage {α : Type} (F : Set α → Set α) : Nat → Set α
  | 0 => ∅
  | t + 1 => F (stage F t)

end Lax751879.LeastFixedPoints
end
