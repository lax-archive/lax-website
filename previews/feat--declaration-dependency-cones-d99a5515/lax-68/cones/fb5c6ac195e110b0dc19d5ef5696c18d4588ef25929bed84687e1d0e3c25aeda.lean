-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.UniversalVerts

-- Lax68.Stars
section
set_option autoImplicit false

namespace Lax68.Stars

def HasStarShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ centre : V,
    centre ∈ G.universalVerts ∧
    ∀ ⦃u v⦄, G.Adj u v → u = centre ∨ v = centre

end Lax68.Stars
end
