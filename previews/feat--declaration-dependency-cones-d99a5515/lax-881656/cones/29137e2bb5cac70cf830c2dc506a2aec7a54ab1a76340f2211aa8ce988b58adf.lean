-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card

-- Lax881656.Cubic
section
set_option autoImplicit false

namespace Lax881656.Cubic

/-- A finite simple graph is cubic when every vertex has degree three. -/
def IsCubic {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v : V, (G.neighborSet v).ncard = 3

end Lax881656.Cubic
end
