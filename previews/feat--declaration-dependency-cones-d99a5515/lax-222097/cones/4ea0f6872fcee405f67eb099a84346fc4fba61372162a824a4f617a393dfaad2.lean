-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax222097.ColumnGraph
section
namespace Lax222097.ColumnGraph.columnGraph
end Lax222097.ColumnGraph.columnGraph

namespace Lax222097.ColumnGraph

open SimpleGraph

abbrev Vertex (R : Type*) (c : ℕ) := R × Fin c × Bool

end Lax222097.ColumnGraph
end
