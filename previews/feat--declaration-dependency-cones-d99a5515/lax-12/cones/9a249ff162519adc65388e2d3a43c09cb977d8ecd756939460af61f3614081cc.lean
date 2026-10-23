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

/-- The set of vertices strongly `r`-reachable from `v` in `G` under the
vertex ordering `π`: the vertices `u` at or before `v` that are the
endpoint of a walk from `v` of length at most `r` all of whose other
vertices come strictly after `v`. Contains `v` itself. -/
def sreach {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) : Set (Fin n) :=
  {u | π u ≤ π v ∧ ∃ w : G.Walk v u, w.length ≤ r ∧
    ∀ y ∈ w.support, y ≠ v → y ≠ u → π v < π y}

end Lax12.ColoringNumbers
end
