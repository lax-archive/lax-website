-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

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
