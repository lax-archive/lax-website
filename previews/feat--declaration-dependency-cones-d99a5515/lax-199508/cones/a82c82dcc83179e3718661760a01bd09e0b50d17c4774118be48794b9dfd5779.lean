-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

-- Lax199508.GraphClasses
section
namespace Lax199508
end Lax199508

namespace Lax199508.GraphClasses
end Lax199508.GraphClasses
end

-- Lax199508.ColoringNumbers
section
namespace Lax199508.ColoringNumbers

open scoped SimpleGraph

open Lax199508.GraphClasses

/-- The set of vertices strongly `r`-reachable from `v` in `G` under the
vertex ordering `π`: the vertices `u` at or before `v` that are the
endpoint of a walk from `v` of length at most `r` all of whose other
vertices come strictly after `v`. Contains `v` itself. -/
def sreach {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) : Set (Fin n) :=
  {u | π u ≤ π v ∧ ∃ w : G.Walk v u, w.length ≤ r ∧
    ∀ y ∈ w.support, y ≠ v → y ≠ u → π v < π y}

end Lax199508.ColoringNumbers
end
