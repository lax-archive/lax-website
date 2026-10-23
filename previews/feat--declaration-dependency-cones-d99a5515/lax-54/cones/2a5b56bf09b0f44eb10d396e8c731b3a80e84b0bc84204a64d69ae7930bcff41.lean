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

-- Lax54.KeyCombLemma
section
namespace Lax54.KeyCombLemma

open Lax54.GraphDefinitions

universe u

/-- The absolute constant in the integral form of the key comb lemma. -/
def keyCombConstant : ℕ := 2 ^ 20

end Lax54.KeyCombLemma
end
