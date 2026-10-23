-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Sym

-- Lax17.Minor
section
namespace Lax17
end Lax17

namespace Lax17.Minor
end Lax17.Minor

namespace Lax17.Minor.Model
end Lax17.Minor.Model
end

-- Lax17.Paths
section
namespace Lax17
end Lax17

namespace Lax17.Paths
end Lax17.Paths

namespace Lax17.Paths.EdgeCutPartition
end Lax17.Paths.EdgeCutPartition

namespace Lax17.Paths.EdgeLinkage
end Lax17.Paths.EdgeLinkage

namespace Lax17.Paths.Path
end Lax17.Paths.Path

namespace Lax17.Paths.VertexLinkage
end Lax17.Paths.VertexLinkage

namespace Lax17.Paths.VertexLinkage.BridgeBetween
end Lax17.Paths.VertexLinkage.BridgeBetween
end

-- Lax17.Linkedness
section
namespace Lax17.Linkedness
end Lax17.Linkedness
end

-- Lax17.PathOfSets
section
namespace Lax17.PathOfSets
end Lax17.PathOfSets

namespace Lax17.PathOfSets.HairyClusterSplit
end Lax17.PathOfSets.HairyClusterSplit

namespace Lax17.PathOfSets.HairySystem
end Lax17.PathOfSets.HairySystem

namespace Lax17.PathOfSets.StrongSystem
end Lax17.PathOfSets.StrongSystem

namespace Lax17.PathOfSets.System
end Lax17.PathOfSets.System

namespace Lax17.PathOfSets.ThreeWayClusterSplit
end Lax17.PathOfSets.ThreeWayClusterSplit
end

-- Lax17.Crossbar
section
namespace Lax17.Crossbar.PseudoGrid
end Lax17.Crossbar.PseudoGrid

namespace Lax17.Crossbar.System
end Lax17.Crossbar.System

namespace Lax17.Crossbar

universe u

open Lax17.Paths

/-- The parameter is an integral power of two. -/
def IsPowerOfTwo (g : ℕ) : Prop :=
  ∃ exponent : ℕ, g = 2 ^ exponent

end Lax17.Crossbar
end
