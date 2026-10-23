-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse

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

def IsInducedMinor {W V : Type*} (H : SimpleGraph W)
    (G : SimpleGraph V) : Prop :=
  Nonempty (Model H G)

end Lax762056.InducedMinors
end

-- Lax762056.Grid
section
namespace Lax762056.Grid

open SimpleGraph InducedMinors

def squareGrid (k : ℕ) : SimpleGraph (Fin k × Fin k) :=
  (pathGraph k).boxProd (pathGraph k)

def ExcludesInducedGrid (k : ℕ) {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ IsInducedMinor (squareGrid k) G

end Lax762056.Grid
end
