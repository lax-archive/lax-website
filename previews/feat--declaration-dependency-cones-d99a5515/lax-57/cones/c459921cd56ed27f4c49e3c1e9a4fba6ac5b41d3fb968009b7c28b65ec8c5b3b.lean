-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Hasse

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

-- Lax57.GraphDefinitions
section
namespace Lax57.GraphDefinitions.Blockade
end Lax57.GraphDefinitions.Blockade

open Finset

open scoped SimpleGraph

namespace Lax57.GraphDefinitions

universe u

/-- The largest cardinality of a clique or stable set. -/
noncomputable abbrev homogeneousNumber {V : Type u} (G : SimpleGraph V) : ℕ :=
  Lax54.GraphDefinitions.homogeneousNumber G

end Lax57.GraphDefinitions
end
