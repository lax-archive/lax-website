-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Lattice

-- Lax751879.LeastFixedPoints
section
namespace Lax751879.LeastFixedPoints.stage
end Lax751879.LeastFixedPoints.stage

namespace Lax751879.LeastFixedPoints

def leastFixedPoint {α : Type} (F : Set α → Set α) : Set α :=
  sInf {R | F R ⊆ R}

axiom fixedPoint {α : Type} (F : Set α → Set α) (hF : Monotone F) :
    F (leastFixedPoint F) = leastFixedPoint F

end Lax751879.LeastFixedPoints
end
