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
namespace Lax54
end Lax54

namespace Lax54.GraphDefinitions
end Lax54.GraphDefinitions

namespace Lax54.GraphDefinitions.StableHubComb
end Lax54.GraphDefinitions.StableHubComb
end

-- Lax57.GraphDefinitions
section
namespace Lax57.GraphDefinitions.Blockade
end Lax57.GraphDefinitions.Blockade

open Finset

open scoped SimpleGraph

namespace Lax57.GraphDefinitions

universe u

/-- The graph induced by `A` has maximum degree at most `|A|/E`. -/
def ESparse {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (A : Finset V) : Prop :=
  ∀ v : {x : V // x ∈ A}, E * (G.induce (A : Set V)).degree v ≤ A.card

/-- One of the two complementary graphs induced by `A` is `1/E`-sparse. -/
def ERestricted {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (E : ℕ) (A : Finset V) : Prop :=
  ESparse G E A ∨ ESparse Gᶜ E A

end Lax57.GraphDefinitions
end
