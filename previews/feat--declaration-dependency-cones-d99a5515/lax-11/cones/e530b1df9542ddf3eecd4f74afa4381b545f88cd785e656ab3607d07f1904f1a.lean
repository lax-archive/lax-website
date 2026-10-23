-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax11.GraphEncoding
section
namespace Lax11.GraphEncoding.EncodesGraph
end Lax11.GraphEncoding.EncodesGraph

namespace Lax11.GraphEncoding

/-- The number of vertices declared by a word: its first entry. -/
def vertexCount (x : List ℕ) : ℕ := x.getD 0 0

end Lax11.GraphEncoding
end
