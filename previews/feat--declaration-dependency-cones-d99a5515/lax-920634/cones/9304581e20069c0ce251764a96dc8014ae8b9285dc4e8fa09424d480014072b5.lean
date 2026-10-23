-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic

-- Lax920634.EdgeExpansion
section
namespace Lax920634
end Lax920634

namespace Lax920634.EdgeExpansion
end Lax920634.EdgeExpansion
end

-- Lax920634.SeedSearch
section
namespace Lax920634.SeedSearch

open Function

/-- A fixed powering exponent sufficient for the lazy permutation seed. -/
def poweringExponent : ℕ := 5760000

/-- The fixed degree of the powered seed. -/
def seedDegree : ℕ := 120 ^ poweringExponent

end Lax920634.SeedSearch
end

-- Lax920634.SeedRotation
section
namespace Lax920634.SeedRotation
end Lax920634.SeedRotation

namespace Lax920634.SeedRotation.lazyRotation
end Lax920634.SeedRotation.lazyRotation

namespace Lax920634.SeedRotation.walkAt
end Lax920634.SeedRotation.walkAt

namespace Lax920634.SeedRotation.walkEnd
end Lax920634.SeedRotation.walkEnd
end

-- Lax920634.ZigZagConstruction
section
namespace Lax920634.ZigZagConstruction.rotation
end Lax920634.ZigZagConstruction.rotation

namespace Lax920634.ZigZagConstruction

open SeedSearch

/-- The fixed degree of each regular graph in the tower. -/
def degree : ℕ := seedDegree ^ 2

/-- The number of vertices in the regular graph at a given level. -/
def baseOrder (k : ℕ) : ℕ := (seedDegree ^ 4) ^ (k + 1)

/-- The number of vertices after path replacement at a given level. -/
def order (k : ℕ) : ℕ := baseOrder k * degree

end Lax920634.ZigZagConstruction
end

-- Lax920634.GraphEncoding
section
namespace Lax920634.GraphEncoding

open SeedSearch ZigZagConstruction

/-- The bounded level-selection loop, carrying the level and current regular order. -/
def levelAfter (b n : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | j + 1, p =>
      let q := levelAfter b n j p
      if q.2 < 2 * n then (q.1 + 1, q.2 * b) else q

/-- The level selected for a requested order, after at most `2*n` advances. -/
def selectedLevel (n : ℕ) : ℕ :=
  (levelAfter (seedDegree ^ 4) n (2 * n) (0, seedDegree ^ 4)).1

end Lax920634.GraphEncoding
end

-- Lax920634.ConstructionSize
section
namespace Lax920634.ConstructionSize

open ZigZagConstruction GraphEncoding SeedSearch

/-- The specified size selector meets the request with a fixed linear upper bound. -/
axiom size_bounds (n : ℕ) :
  n ≤ order (selectedLevel n) ∧
  order (selectedLevel n) ≤
    (2 * degree * seedDegree ^ 4) * (n + 1)

end Lax920634.ConstructionSize
end
