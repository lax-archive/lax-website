-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card

-- Lax117284.BipartiteMatching
section
namespace Lax117284.BipartiteMatching

variable {V : Type*} (G : SimpleGraph V)

/-- **A subgraph saturates a set of vertices** when it contains every one of them. -/
def Saturates (M : G.Subgraph) (S : Set V) : Prop := S ⊆ M.verts

end Lax117284.BipartiteMatching
end
