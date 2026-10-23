-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy

-- Lax54.GraphDefinitions
section
namespace Lax54.GraphDefinitions.StableHubComb
end Lax54.GraphDefinitions.StableHubComb

open Finset

open scoped SimpleGraph

namespace Lax54.GraphDefinitions

universe u

/-- The largest cardinality of a clique or stable set in a finite graph. -/
noncomputable def homogeneousNumber {V : Type u} (G : SimpleGraph V) : ℕ :=
  max G.cliqueNum G.indepNum

end Lax54.GraphDefinitions
end
