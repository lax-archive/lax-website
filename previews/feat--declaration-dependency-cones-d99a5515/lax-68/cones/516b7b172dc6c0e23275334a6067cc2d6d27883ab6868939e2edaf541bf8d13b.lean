-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths

-- Lax68.GraphMinors
section
namespace Lax68
end Lax68

namespace Lax68.GraphMinors
end Lax68.GraphMinors

namespace Lax68.GraphMinors.MinorModel
end Lax68.GraphMinors.MinorModel
end

-- Lax68.GraphTopologicalMinors
section
set_option autoImplicit false

namespace Lax68.GraphTopologicalMinors

def walkInterior {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) : Set V :=
  {x | x ∈ P.support ∧ x ≠ a ∧ x ≠ b}

structure TopologicalMinorModel {W V : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  branch : W ↪ V
  route :
    ∀ {a b : W}, H.Adj a b →
      G.Walk (branch a) (branch b)
  route_isPath :
    ∀ {a b : W} (h : H.Adj a b),
      (route h).IsPath
  branch_avoids_interiors :
    ∀ {a b : W} (h : H.Adj a b) (w : W),
      branch w ∉ walkInterior (route h)
  route_interiors_disjoint :
    ∀ {a b c d : W}
        (hab : H.Adj a b) (hcd : H.Adj c d),
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
        Disjoint
          (walkInterior (route hab))
          (walkInterior (route hcd))

end Lax68.GraphTopologicalMinors
end
