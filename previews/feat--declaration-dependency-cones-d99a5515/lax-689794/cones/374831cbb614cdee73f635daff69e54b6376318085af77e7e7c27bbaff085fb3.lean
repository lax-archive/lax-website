-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.Lattice

-- Lax228581.Treewidth
section
namespace Lax228581
end Lax228581

namespace Lax228581.Treewidth
end Lax228581.Treewidth

namespace Lax228581.Treewidth.TreeDecomposition
end Lax228581.Treewidth.TreeDecomposition
end

-- Lax689794.GraphWords
section
namespace Lax689794.GraphWords.NiceDecomposition
end Lax689794.GraphWords.NiceDecomposition

namespace Lax689794.GraphWords.bagAt
end Lax689794.GraphWords.bagAt

namespace Lax689794.GraphWords

open Lax228581.Treewidth

open Classical in
/-- **`g` is the word of the graph `G`**: the number of vertices, then the adjacency matrix row
by row. -/
structure EncodesGraph {n : ℕ} (g : List ℕ) (G : SimpleGraph (Fin n)) : Prop where
  /-- The word is the count followed by the matrix. -/
  length_eq : g.length = 1 + n * n
  /-- The first entry is the number of vertices. -/
  head_eq : g.getD 0 0 = n
  /-- The entry of the row `u` and column `v` is `1` when the two vertices are adjacent and `0`
  otherwise. -/
  adj_eq : ∀ u v : Fin n, g.getD (1 + u.val * n + v.val) 0 = if G.Adj u v then 1 else 0

end Lax689794.GraphWords
end
