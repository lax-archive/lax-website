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

end Lax916827.SnakeGraphs
end
