-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

-- Lax683916.TwoUniformSetSystems
section
namespace Lax683916.TwoUniformSetSystems

/-- A family of two-element subsets of `V`. -/
structure TwoUniformSetSystem (V : Type*) where
  /-- The sets belonging to the family. -/
  sets : Set (Set V)
  /-- Every member of the family has exactly two elements. -/
  twoUniform : ∀ s ∈ sets, Set.ncard s = 2

end Lax683916.TwoUniformSetSystems
end

-- Lax683916.SetSystemRepresentation
section
namespace Lax683916.SetSystemRepresentation

open Lax683916.TwoUniformSetSystems

universe u

/-- An equivalence that sends graph edges to their two-element endpoint sets. -/
structure RepresentationEquiv (V : Type u) where
  /-- The equivalence between the two representation types. -/
  toEquiv : SimpleGraph V ≃ TwoUniformSetSystem V
  /-- A pair belongs to the image set system exactly when its two elements are adjacent. -/
  map_pair : ∀ (G : SimpleGraph V) (u v : V),
    {u, v} ∈ (toEquiv G).sets ↔ G.Adj u v

end Lax683916.SetSystemRepresentation
end
