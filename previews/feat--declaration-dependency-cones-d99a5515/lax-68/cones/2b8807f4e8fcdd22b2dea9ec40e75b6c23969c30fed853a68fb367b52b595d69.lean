-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Hasse

-- Lax68.Ladders
section
set_option autoImplicit false

namespace Lax68.Ladders

def HasLadderShape {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ,
    0 < n ∧
    Nonempty
      (G ≃g (SimpleGraph.pathGraph n □ SimpleGraph.pathGraph 2))

def IsLadder {V : Type*} (G : SimpleGraph V) : Prop :=
  HasLadderShape G

end Lax68.Ladders
end
