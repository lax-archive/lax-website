-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Hasse

-- Lax68.Paths
section
set_option autoImplicit false

namespace Lax68.Paths

def HasPathShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ,
    0 < n ∧
    Nonempty (G ≃g SimpleGraph.pathGraph n)

def IsPath {V : Type*} (G : SimpleGraph V) : Prop :=
  HasPathShape G

end Lax68.Paths
end
