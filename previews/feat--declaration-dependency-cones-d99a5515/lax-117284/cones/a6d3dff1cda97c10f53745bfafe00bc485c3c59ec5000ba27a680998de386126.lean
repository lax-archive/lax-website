-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

-- Lax271696.GraphEncoding
section
namespace Lax271696
end Lax271696

namespace Lax271696.GraphEncoding
end Lax271696.GraphEncoding

namespace Lax271696.GraphEncoding.EncodesGraph
end Lax271696.GraphEncoding.EncodesGraph
end

-- Lax117284.BipartiteGraph
section
namespace Lax117284.BipartiteGraph

open Lax271696.GraphEncoding

/-- The number of left vertices a word declares: its last entry. -/
def leftCount (x : List ℕ) : ℕ := x.getLastD 0

end Lax117284.BipartiteGraph
end
