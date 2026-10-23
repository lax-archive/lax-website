-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse

-- Lax222097.InducedMinors
section
namespace Lax222097
end Lax222097

namespace Lax222097.InducedMinors
end Lax222097.InducedMinors

namespace Lax222097.InducedMinors.Model
end Lax222097.InducedMinors.Model
end

-- Lax222097.Grid
section
namespace Lax222097.Grid

open SimpleGraph InducedMinors

def squareGrid (k : ℕ) : SimpleGraph (Fin k × Fin k) :=
  (pathGraph k).boxProd (pathGraph k)

end Lax222097.Grid
end
