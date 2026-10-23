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
namespace Lax689794.GraphWords.EncodesGraph
end Lax689794.GraphWords.EncodesGraph

namespace Lax689794.GraphWords.NiceDecomposition
end Lax689794.GraphWords.NiceDecomposition

namespace Lax689794.GraphWords

open Lax228581.Treewidth

/-- The kind of node `i`: `0` leaf, `1` introduce, `2` forget, `3` join. -/
def kind (D : List ℕ) (i : ℕ) : ℕ := D.getD (1 + 3 * i) 0

/-- The vertex of node `i`, for an introduce or a forget node. -/
def vertex (D : List ℕ) (i : ℕ) : ℕ := D.getD (2 + 3 * i) 0

/-- The bag of node `i` among the vertices `0 … n - 1`, from the leaves up: the empty bag at a
leaf, the child's bag plus the vertex at an introduce node, minus it at a forget node, and the
child's bag at a join node. The first child of node `i + 1` is node `i`. -/
def bagAt (n : ℕ) (D : List ℕ) : ℕ → Finset (Fin n)
  | 0 => ∅
  | i + 1 =>
      if kind D (i + 1) = 1 then
        if h : vertex D (i + 1) < n then insert ⟨vertex D (i + 1), h⟩ (bagAt n D i)
        else bagAt n D i
      else if kind D (i + 1) = 2 then
        if h : vertex D (i + 1) < n then (bagAt n D i).erase ⟨vertex D (i + 1), h⟩
        else bagAt n D i
      else if kind D (i + 1) = 3 then bagAt n D i
      else ∅

end Lax689794.GraphWords
end
