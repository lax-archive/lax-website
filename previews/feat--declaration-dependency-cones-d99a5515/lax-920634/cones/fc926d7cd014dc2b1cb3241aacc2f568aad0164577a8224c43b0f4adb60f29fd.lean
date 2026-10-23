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
namespace Lax920634
end Lax920634

namespace Lax920634.SeedSearch
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
namespace Lax920634.ZigZagConstruction
end Lax920634.ZigZagConstruction

namespace Lax920634.ZigZagConstruction.rotation
end Lax920634.ZigZagConstruction.rotation
end

-- Lax920634.GraphEncoding
section
namespace Lax920634.GraphEncoding.levelAfter
end Lax920634.GraphEncoding.levelAfter

namespace Lax920634.GraphEncoding

open SeedSearch ZigZagConstruction

/-- A Boolean serialized as an empty or singleton-empty bracketed list. -/
def encodeBit (b : Bool) : List Bool :=
  if b then [false, false, true, true] else [false, true]

/-- Serialize a Boolean word as a bracketed list of encoded Booleans. -/
def encodeWord (w : List Bool) : List Bool := false :: (w.flatMap encodeBit ++ [true])

/-- Serialize a pair of natural coordinates, each represented in unary. -/
def encodeRecord (p : ℕ × ℕ) : List Bool :=
  false :: (encodeWord (List.replicate p.1 true) ++
    encodeWord (List.replicate p.2 true) ++ [true])

end Lax920634.GraphEncoding
end
