-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.List.FinRange

-- Lax323828.Graphs
section
namespace Lax323828.Graphs

/-- A simple graph represented by a symmetric Boolean adjacency matrix with zero diagonal. -/
structure Graph (n : ℕ) where
  /-- Whether the two labeled vertices are adjacent. -/
  adjacent : Fin n → Fin n → Bool
  /-- No vertex is adjacent to itself. -/
  loopless : ∀ v, adjacent v v = false
  /-- Adjacency is unchanged when the endpoints are exchanged. -/
  symmetric : ∀ u v, adjacent u v = adjacent v u

/-- Read the Boolean matrix as a mathematical simple graph. -/
def Graph.simpleGraph {n : ℕ} (G : Graph n) : SimpleGraph (Fin n) where
  Adj u v := G.adjacent u v = true
  symm := ⟨fun u v h ↦ (G.symmetric u v).symm.trans h⟩
  loopless := ⟨fun v h ↦ Bool.noConfusion ((G.loopless v).symm.trans h)⟩

/-- The maximum number of pairwise adjacent vertices. -/
noncomputable def Graph.cliqueNumber {n : ℕ} (G : Graph n) : ℕ :=
  G.simpleGraph.cliqueNum

end Lax323828.Graphs
end
