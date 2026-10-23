-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Lattice

-- Lax979537.LeastFixedPoints
section
namespace Lax979537.LeastFixedPoints.stage
end Lax979537.LeastFixedPoints.stage

namespace Lax979537.LeastFixedPoints

def leastFixedPoint {α : Type} (F : Set α → Set α) : Set α :=
  sInf {R | F R ⊆ R}

axiom least {α : Type} (F : Set α → Set α) (R : Set α)
    (hR : F R ⊆ R) : leastFixedPoint F ⊆ R

end Lax979537.LeastFixedPoints
end
