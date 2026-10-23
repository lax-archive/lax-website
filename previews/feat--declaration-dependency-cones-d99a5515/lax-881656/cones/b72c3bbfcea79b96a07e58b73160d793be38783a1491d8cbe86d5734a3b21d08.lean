-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Bipartite

-- Lax881656.Bipartite
section
set_option autoImplicit false

namespace Lax881656.Bipartite

/-- A simple graph is bipartite when it is properly colorable with two colors. -/
def IsBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Colorable 2

end Lax881656.Bipartite
end
