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

/-- The product `ω(G) · α(G)` used in the critical-graph argument. -/
noncomputable def kappa {V : Type u} (G : SimpleGraph V) : ℕ :=
  G.cliqueNum * G.indepNum

/--
A graph is `q`-critical if `kappa G ^ q < |V(G)|`, while every proper
vertex-induced subgraph `G[S]` satisfies `|S| ≤ kappa (G[S]) ^ q`.
-/
def IsQCritical {V : Type u} [Fintype V] (q : ℕ) (G : SimpleGraph V) : Prop :=
  kappa G ^ q < Fintype.card V ∧
    ∀ S : Finset V, S.card < Fintype.card V →
      S.card ≤ kappa (G.induce (S : Set V)) ^ q

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

/-- `q`-criticality for the product `ω(G)α(G)`. -/
abbrev IsQCritical {V : Type u} [Fintype V] (q : ℕ) (G : SimpleGraph V) : Prop :=
  Lax54.GraphDefinitions.IsQCritical q G

end Lax57.GraphDefinitions
end
