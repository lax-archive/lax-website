-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Equiv.Fin.Basic

-- Lax920634.SeedSearch
section
namespace Lax920634
end Lax920634

namespace Lax920634.SeedSearch
end Lax920634.SeedSearch
end

-- Lax920634.SeedRotation
section
namespace Lax920634.SeedRotation.lazyRotation
end Lax920634.SeedRotation.lazyRotation

namespace Lax920634.SeedRotation.walkAt
end Lax920634.SeedRotation.walkAt

namespace Lax920634.SeedRotation

open SeedSearch

/-- Follow a finite sequence of numbered darts to its endpoint. -/
def walkEnd {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d) :
    (t : ℕ) → Fin n → (Fin t → Fin d) → Fin n
  | 0, v, _ => v
  | t + 1, v, s => walkEnd R t (R (v, s 0)).1 (fun j => s j.succ)

end Lax920634.SeedRotation
end
