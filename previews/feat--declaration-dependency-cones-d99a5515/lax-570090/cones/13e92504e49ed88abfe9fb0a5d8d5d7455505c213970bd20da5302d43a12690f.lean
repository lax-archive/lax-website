-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Real.Basic

-- Lax570090.VertexRemovalStability
section
namespace Lax570090.VertexRemovalStability

open SimpleGraph

/-- The number of (unordered) edges of a finite simple graph. -/
noncomputable def edgeCount {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

end Lax570090.VertexRemovalStability
end
