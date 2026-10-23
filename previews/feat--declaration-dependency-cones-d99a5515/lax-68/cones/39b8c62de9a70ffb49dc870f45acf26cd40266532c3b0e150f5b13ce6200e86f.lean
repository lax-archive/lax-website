-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths

-- Lax68.GraphMinors
section
namespace Lax68
end Lax68

namespace Lax68.GraphMinors
end Lax68.GraphMinors

namespace Lax68.GraphMinors.MinorModel
end Lax68.GraphMinors.MinorModel
end

-- Lax68.GraphTopologicalMinors
section
namespace Lax68.GraphTopologicalMinors.TopologicalMinorModel
end Lax68.GraphTopologicalMinors.TopologicalMinorModel

set_option autoImplicit false

namespace Lax68.GraphTopologicalMinors

def walkInterior {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) : Set V :=
  {x | x ∈ P.support ∧ x ≠ a ∧ x ≠ b}

end Lax68.GraphTopologicalMinors
end
