-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

-- Lax199508.GraphClasses
section
namespace Lax199508.GraphClasses

/-- A class of finite simple graphs: for each number of vertices `n`, a
predicate on the simple graphs over the canonical `n`-element type. -/
abbrev GraphClass : Type := ∀ n : ℕ, SimpleGraph (Fin n) → Prop

end Lax199508.GraphClasses
end

-- Lax199508.NowhereDenseClasses
section
namespace Lax199508.NowhereDenseClasses

open Lax199508.GraphClasses

/-- A model of `H` as a depth-`r` minor of `G`: pairwise disjoint branch
sets, each spanned by walks of length at most `r` from a center vertex
(hence connected of radius at most `r`), with an edge of `G` between the
branch sets of any two adjacent vertices of `H`. -/
structure ShallowMinorModel {V W : Type*} (r : ℕ) (H : SimpleGraph W)
    (G : SimpleGraph V) where
  /-- The branch set of each vertex of `H`. -/
  branch : W → Set V
  /-- The center of each branch set. -/
  center : W → V
  /-- Centers lie in their branch sets (so branch sets are nonempty). -/
  center_mem : ∀ u, center u ∈ branch u
  /-- Distinct branch sets are disjoint. -/
  disjoint : ∀ u v, u ≠ v → Disjoint (branch u) (branch v)
  /-- Every vertex of a branch set is reached from the center by a walk
  of length at most `r` inside the branch set. -/
  radius_le : ∀ u, ∀ x ∈ branch u, ∃ w : G.Walk (center u) x,
    w.length ≤ r ∧ ∀ y ∈ w.support, y ∈ branch u
  /-- Adjacent vertices of `H` have adjacent branch sets. -/
  adj : ∀ u v, H.Adj u v → ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y

/-- `H` is a minor of `G` at depth `r`. -/
def HasShallowMinor {V W : Type*} (G : SimpleGraph V) (r : ℕ)
    (H : SimpleGraph W) : Prop :=
  Nonempty (ShallowMinorModel r H G)

/-- A graph class is nowhere dense if for every depth `r` some complete
graph is not a depth-`r` minor of any member. -/
def NowhereDense (C : GraphClass) : Prop :=
  ∀ r : ℕ, ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ¬ HasShallowMinor G r (⊤ : SimpleGraph (Fin t))

end Lax199508.NowhereDenseClasses
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

-- Lax3.NowhereDenseSplitter
section
namespace Lax3.NowhereDenseSplitter

open Lax3.SplitterGame

open Lax199508.GraphClasses Lax199508.NowhereDenseClasses

/-- On a nowhere dense class, for every radius there are round and
batch bounds with which Splitter wins the isolation splitter game on
every member. -/
axiom splitterWins_of_nowhereDense (C : GraphClass) (h : NowhereDense C)
    (r : ℕ) :
    ∃ ℓ m : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      SplitterWins m r ℓ G

end Lax3.NowhereDenseSplitter
end
