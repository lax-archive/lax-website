-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Set.Card

-- Lax916827.SnakeGraphs
section
namespace Lax916827.SnakeGraphs.IsSnakePath
end Lax916827.SnakeGraphs.IsSnakePath

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

end Lax916827.SnakeGraphs
end
