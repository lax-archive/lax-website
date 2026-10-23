-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

-- Lax199508.GraphClasses
section
namespace Lax199508
end Lax199508

namespace Lax199508.GraphClasses
end Lax199508.GraphClasses
end

-- Lax199508.UniformQuasiWideness
section
namespace Lax199508.UniformQuasiWideness

open Lax199508.GraphClasses

/-- `G` with the vertices of `S` isolated: every edge incident to `S` is
removed and the vertex type is unchanged. This models `G − S`. -/
def deleteVerts {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

end Lax199508.UniformQuasiWideness
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

-- Lax3.SplitterGame
section
namespace Lax3.SplitterGame

open Lax3.ColoredGraphs

open Lax199508.UniformQuasiWideness

/-- Winning positions of Splitter in the (`ℓ`, `m`, `r`)-isolation
splitter game, by recursion on the remaining budget `ℓ`: the arena `G`
is already edgeless, or a round is left and for every vertex Connector
plays there is a batch of at most `m` vertices of its `r`-ball whose
isolation, after restricting the arena to that ball, is a winning
position with one round fewer. -/
def SplitterWins {n : ℕ} (m r : ℕ) : ℕ → SimpleGraph (Fin n) → Prop
  | 0, G => G = ⊥
  | ℓ + 1, G => G = ⊥ ∨
      ∀ v : Fin n, ∃ W : Set (Fin n), W ⊆ ball G r v ∧ W.ncard ≤ m ∧
        SplitterWins m r ℓ (deleteVerts (deleteVerts G (ball G r v)ᶜ) W)

end Lax3.SplitterGame
end
