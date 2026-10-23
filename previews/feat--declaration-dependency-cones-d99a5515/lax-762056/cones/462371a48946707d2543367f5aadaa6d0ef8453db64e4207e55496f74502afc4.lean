-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse

-- Lax762056.InducedMinors
section
namespace Lax762056
end Lax762056

namespace Lax762056.InducedMinors
end Lax762056.InducedMinors

namespace Lax762056.InducedMinors.Model
end Lax762056.InducedMinors.Model
end

-- Lax762056.Grid
section
namespace Lax762056.Grid

open SimpleGraph InducedMinors

def squareGrid (k : ℕ) : SimpleGraph (Fin k × Fin k) :=
  (pathGraph k).boxProd (pathGraph k)

end Lax762056.Grid
end
