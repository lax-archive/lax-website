-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Hasse

-- Lax68.GridsAndWalls
section
set_option autoImplicit false

namespace Lax68.GridsAndWalls

def HasGridShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ m n : ℕ,
    0 < m ∧
    0 < n ∧
    Nonempty
      (G ≃g (SimpleGraph.pathGraph m □ SimpleGraph.pathGraph n))

def IsGrid {V : Type*} (G : SimpleGraph V) : Prop :=
  HasGridShape G

end Lax68.GridsAndWalls
end
