-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Basic

-- Lax683916.NeighborhoodSetSystems
section
namespace Lax683916.NeighborhoodSetSystems

universe u

/-- A vertex-indexed family of open neighborhoods. -/
structure NeighborhoodSetSystem (V : Type u) where
  /-- The open neighborhood assigned to each vertex. -/
  neighborhood : V → Set V
  /-- Neighborhood membership is symmetric. -/
  symmetric : ∀ u v : V, v ∈ neighborhood u ↔ u ∈ neighborhood v
  /-- A vertex does not belong to its own open neighborhood. -/
  loopless : ∀ u : V, u ∉ neighborhood u

end Lax683916.NeighborhoodSetSystems
end

-- Lax683916.NeighborhoodSetSystemRepresentation
section
namespace Lax683916.NeighborhoodSetSystemRepresentation

open Lax683916.NeighborhoodSetSystems

universe u

/-- An equivalence that sends every graph to its vertex-indexed open neighborhoods. -/
structure RepresentationEquiv (V : Type u) where
  /-- The equivalence between simple graphs and neighborhood set systems. -/
  toEquiv : SimpleGraph V ≃ NeighborhoodSetSystem V
  /-- Membership in the image neighborhood is exactly adjacency. -/
  map_mem : ∀ (G : SimpleGraph V) (u v : V),
    v ∈ (toEquiv G).neighborhood u ↔ G.Adj u v

end Lax683916.NeighborhoodSetSystemRepresentation
end
