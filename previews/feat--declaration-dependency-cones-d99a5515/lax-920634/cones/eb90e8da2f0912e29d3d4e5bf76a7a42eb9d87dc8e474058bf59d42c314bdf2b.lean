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

namespace Lax920634.SeedRotation

open SeedSearch

/-- Follow a finite sequence of numbered darts to its endpoint. -/
def walkEnd {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d) :
    (t : ℕ) → Fin n → (Fin t → Fin d) → Fin n
  | 0, v, _ => v
  | t + 1, v, s => walkEnd R t (R (v, s 0)).1 (fun j => s j.succ)

/-- The vertex reached after a prescribed number of steps of a finite dart sequence. -/
def walkAt {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (t : ℕ) (v : Fin n) (s : Fin t → Fin d) : ℕ → Fin n
  | 0 => v
  | k + 1 => if h : k < t then
    (R (walkAt R t v s k, s ⟨k, h⟩)).1 else walkAt R t v s k

/-- The edge rotation of a graph power, with dart sequences numbered in base `d`. -/
def powerRotation {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (t : ℕ) (p : Fin n × Fin (d ^ t)) : Fin n × Fin (d ^ t) :=
  let s := finFunctionFinEquiv.symm p.2
  (walkEnd R t p.1 s, finFunctionFinEquiv (fun j =>
    (R (walkAt R t p.1 s (Fin.rev j).val, s (Fin.rev j))).2))

end Lax920634.SeedRotation
end
