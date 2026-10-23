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

/-- The set of vertices weakly `r`-reachable from `v` in `G` under the
vertex ordering `π` (vertex `u` sits at position `π u`): the endpoints
`u` of walks from `v` of length at most `r` on whose support `u` is
`π`-minimal. Contains `v` itself. -/
def wreach {n : ℕ} (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (r : ℕ) (v : Fin n) : Set (Fin n) :=
  {u | ∃ w : G.Walk v u, w.length ≤ r ∧ ∀ y ∈ w.support, π u ≤ π y}

end Lax199508.ColoringNumbers
end

-- Lax3.ColoredGraphs
section
namespace Lax3.ColoredGraphs

/-- The vertices `u` and `v` are within distance `d` in `G`: some walk
from `u` to `v` has length at most `d`. -/
def WithinDist {V : Type*} (G : SimpleGraph V) (d : ℕ) (u v : V) : Prop :=
  ∃ w : G.Walk u v, w.length ≤ d

/-- The ball of radius `r` around `v` in `G`: the vertices within
distance `r` of `v`. -/
def ball {V : Type*} (G : SimpleGraph V) (r : ℕ) (v : V) : Set V :=
  {u | WithinDist G r v u}

end Lax3.ColoredGraphs
end

-- Lax3.NeighborhoodCovers
section
namespace Lax3.NeighborhoodCovers

open Lax3.ColoredGraphs

/-- `X` is an `r`-neighborhood cover of `G` of radius `2r` and degree
`d`: every `r`-ball is inside some cluster, the cluster of `u` lies in
the `2r`-ball of `u`, and no vertex is in more than `d` clusters. -/
structure IsNeighborhoodCover {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ)
    (X : Fin n → Set (Fin n)) (d : ℕ) : Prop where
  /-- Every `r`-ball is contained in some cluster. -/
  ball_subset : ∀ v : Fin n, ∃ u : Fin n, ball G r v ⊆ X u
  /-- Each cluster lies in the `2r`-ball of its center. -/
  subset_ball : ∀ u : Fin n, X u ⊆ ball G (2 * r) u
  /-- No vertex belongs to more than `d` clusters. -/
  degree_le : ∀ v : Fin n, {u : Fin n | v ∈ X u}.ncard ≤ d

end Lax3.NeighborhoodCovers
end

-- Lax3.OrderedNeighborhoodCover
section
namespace Lax3.OrderedNeighborhoodCover

open Lax3.NeighborhoodCovers

open Lax199508.ColoringNumbers

/-- The fibers of weak `2r`-reachability under any ordering `π` form
an `r`-neighborhood cover of radius `2r` and degree at most `k`,
provided every weak `2r`-reachability set has size at most `k`.
This is the arbitrary-order construction of Lemma 6.9 of
Grohe–Kreutzer–Siebertz, used both by the algorithm with its computed
ordering and by the existential cover theorem with an optimal one. -/
axiom isNeighborhoodCover_wreach {n : ℕ} (G : SimpleGraph (Fin n)) (r k : ℕ)
    (π : Equiv.Perm (Fin n)) (hk : ∀ v, (wreach G π (2 * r) v).ncard ≤ k) :
    IsNeighborhoodCover G r (fun u => {w | u ∈ wreach G π (2 * r) w}) k

end Lax3.OrderedNeighborhoodCover
end
