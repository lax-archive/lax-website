-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Set.Card

-- Lax916827.SnakeGraphs
section
namespace Lax916827.SnakeGraphs

/-- The alphabet `C` of snake letters for the state set `Q` and output alphabet `B`:
a letter gives, for every vertex of the two copies of `Q`, its outgoing edge to
the other copy with a label in `B + 1`, if any. -/
abbrev SnakeLetter (Q B : Type) := Bool × Q → Option (Q × Option B)

/-- A vertex of a snake graph: a row `q` and a column `i`. -/
abbrev Vtx (Q : Type) := Q × ℕ

/-- The edge relation of the graph represented by `w`: an edge from `v` to `v'`
labelled `o` is recorded by the letter between their columns, read from the left
copy when `v'` is in the next column and from the right copy when it is in the
previous one. -/
def Edge {Q B : Type} (w : List (SnakeLetter Q B)) (v v' : Vtx Q) (o : Option B) : Prop :=
  (v'.2 = v.2 + 1 ∧ ∃ c, w[v.2]? = some c ∧ c (false, v.1) = some (v'.1, o)) ∨
  (v.2 = v'.2 + 1 ∧ ∃ c, w[v'.2]? = some c ∧ c (true, v.1) = some (v'.1, o))

/-- All edges of the graph represented by `w` lie on the single directed path
`p 0, …, p m` with pairwise distinct vertices and edge labels `lab`: this is
what makes the graph a snake graph. -/
structure IsSnakePath {Q B : Type} (w : List (SnakeLetter Q B)) (m : ℕ) (p : ℕ → Vtx Q)
    (lab : ℕ → Option B) : Prop where
  /-- Consecutive vertices of the path are joined by an edge with the recorded
  label. -/
  edge : ∀ t < m, Edge w (p t) (p (t + 1)) (lab t)
  /-- The vertices of the path are pairwise distinct. -/
  inj : ∀ s ≤ m, ∀ t ≤ m, p s = p t → s = t
  /-- Every edge of the graph is an edge of the path. -/
  covers : ∀ v v' o, Edge w v v' o → ∃ t < m, p t = v ∧ p (t + 1) = v' ∧ lab t = o

end Lax916827.SnakeGraphs
end
