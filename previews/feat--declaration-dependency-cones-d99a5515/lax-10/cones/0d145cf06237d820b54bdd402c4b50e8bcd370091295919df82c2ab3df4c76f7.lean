-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

-- Lax10.ThreeConnectedAndColorable
section
open Finset

namespace Lax10.ThreeConnectedAndColorable

universe u

variable {V : Type u}

/-- A simple graph is colorable with at most $m$ colors. -/
def KColorable (m : Nat) (G : SimpleGraph V) : Prop :=
  G.Colorable m

end Lax10.ThreeConnectedAndColorable
end
