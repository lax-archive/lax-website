-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

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
