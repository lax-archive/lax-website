-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

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
