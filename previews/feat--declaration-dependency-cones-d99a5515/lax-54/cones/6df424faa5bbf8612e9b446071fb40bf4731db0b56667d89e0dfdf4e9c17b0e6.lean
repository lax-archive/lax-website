-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy

-- Lax54.GraphDefinitions
section
namespace Lax54
end Lax54

namespace Lax54.GraphDefinitions
end Lax54.GraphDefinitions

namespace Lax54.GraphDefinitions.StableHubComb
end Lax54.GraphDefinitions.StableHubComb
end

-- Lax54.BipartiteCombLemma
section
namespace Lax54.BipartiteCombLemma.CombBetween
end Lax54.BipartiteCombLemma.CombBetween

namespace Lax54.BipartiteCombLemma

universe u

/-- The sparse alternative in the `d = 1/2` case of Theorem 2.1. -/
def SmallSideBound (C Gamma Delta b : ℕ) : Prop :=
  b ^ 2 ≤ C ^ 2 * Gamma * Delta

end Lax54.BipartiteCombLemma
end
