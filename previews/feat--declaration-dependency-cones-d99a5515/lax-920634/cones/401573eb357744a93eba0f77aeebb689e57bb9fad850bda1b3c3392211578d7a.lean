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

end Lax920634.ZigZagConstruction
end

-- Lax920634.GraphEncoding
section
namespace Lax920634.GraphEncoding
end Lax920634.GraphEncoding

namespace Lax920634.GraphEncoding.levelAfter
end Lax920634.GraphEncoding.levelAfter
end

-- Lax920634.WordEncoding
section
namespace Lax920634.WordEncoding

open ZigZagConstruction GraphEncoding

/-- Decode the matching table at its declared graph order. Path edges are determined by row numbers. -/
def decode (n : ℕ) (tape : List ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v =>
    (u.val / degree = v.val / degree ∧ u.val+1 = v.val) ∨
      v.val = (tape.tail[u.val]?).getD 0)

end Lax920634.WordEncoding
end
