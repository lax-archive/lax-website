-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Hasse

-- Lax68.GridsAndWalls
section
set_option autoImplicit false

namespace Lax68.GridsAndWalls

def consecutive (a b : ℕ) : Prop :=
  a + 1 = b ∨ b + 1 = a

def WallAdjacent {m n : ℕ} (u v : Fin m × Fin n) : Prop :=
  (u.1 = v.1 ∧ consecutive u.2.val v.2.val) ∨
  (u.2 = v.2 ∧
    consecutive u.1.val v.1.val ∧
    (Nat.min u.1.val v.1.val + u.2.val) % 2 = 0)

end Lax68.GridsAndWalls
end
