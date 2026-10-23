-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Set.Card

-- Lax916827.SnakeGraphs
section
namespace Lax916827.SnakeGraphs.IsSnakePath
end Lax916827.SnakeGraphs.IsSnakePath

namespace Lax916827.SnakeGraphs

/-- The output along a path: the concatenation of the labels of its edges, the
label `none` contributing nothing. -/
def pathOut {B : Type} (lab : ℕ → Option B) (m : ℕ) : List B :=
  ((List.range m).map (fun t => (lab t).toList)).flatten

end Lax916827.SnakeGraphs
end
