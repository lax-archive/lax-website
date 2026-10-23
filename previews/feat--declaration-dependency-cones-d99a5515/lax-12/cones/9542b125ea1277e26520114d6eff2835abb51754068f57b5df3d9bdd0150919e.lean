-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax12.GraphClasses
section
namespace Lax12
end Lax12

namespace Lax12.GraphClasses
end Lax12.GraphClasses
end

-- Lax12.ColoringNumbers
section
namespace Lax12.ColoringNumbers

open scoped SimpleGraph

open Lax12.GraphClasses

/-- The set of vertices weakly `r`-reachable from `v` in `G` under the
vertex ordering `π` (vertex `u` sits at position `π u`): the endpoints
`u` of walks from `v` of length at most `r` on whose support `u` is
`π`-minimal. Contains `v` itself. -/
def wreach {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) : Set (Fin n) :=
  {u | ∃ w : G.Walk v u, w.length ≤ r ∧ ∀ y ∈ w.support, π u ≤ π y}

end Lax12.ColoringNumbers
end
