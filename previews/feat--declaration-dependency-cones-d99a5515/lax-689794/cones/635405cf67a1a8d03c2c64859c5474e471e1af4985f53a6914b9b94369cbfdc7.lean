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

namespace Lax689794.GraphWords.bagAt
end Lax689794.GraphWords.bagAt

namespace Lax689794.GraphWords

open Lax228581.Treewidth

/-- The second child of node `i`, for a join node. -/
def other (D : List ℕ) (i : ℕ) : ℕ := D.getD (3 + 3 * i) 0

end Lax689794.GraphWords
end
