-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

-- Lax762056.InducedMinors
section
namespace Lax762056.InducedMinors

open SimpleGraph

structure Model {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) where
  branch : W → Set V
  connected : ∀ v, Connected (G.induce (branch v))
  disjoint : ∀ u v, u ≠ v → Disjoint (branch u) (branch v)
  adjacent : ∀ u v, u ≠ v →
    (H.Adj u v ↔ ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y)

end Lax762056.InducedMinors
end
