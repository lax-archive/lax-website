-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Paths

-- Lax762056.AsteroidalCycles
section
namespace Lax762056.AsteroidalCycles

open SimpleGraph

def AvoidsClosedNeighborhood {V : Type*} (G : SimpleGraph V)
    (S T : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ T, x ≠ y ∧ ¬ G.Adj x y

def HasAsteroidalCycleTriple {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (base : Fin 3 → V) (cycle : ∀ i, Walk G (base i) (base i)),
    (∀ i, (cycle i).IsCycle) ∧
    (Pairwise fun i j => AvoidsClosedNeighborhood G
      {v | v ∈ (cycle i).support} {v | v ∈ (cycle j).support}) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ∃ u ∈ (cycle i).support, ∃ v ∈ (cycle j).support,
        ∃ p : Path G u v, AvoidsClosedNeighborhood G
          {x | x ∈ p.val.support} {x | x ∈ (cycle k).support})

end Lax762056.AsteroidalCycles
end

-- Lax762056.ColumnGraph
section
namespace Lax762056.ColumnGraph

open SimpleGraph

abbrev Vertex (R : Type*) (c : ℕ) := R × Fin c × Bool

def columnGraph (R : Type*) (c : ℕ) : SimpleGraph (Vertex R c) :=
  fromRel fun (row, column, side) (row', column', side') =>
    (column = column' ∧ side ≠ side') ∨
    (row = row' ∧ (column.val + 1 = column'.val ∨ column'.val + 1 = column.val))

end Lax762056.ColumnGraph
end

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
end Lax762056.Grid
end

-- Lax762056.CycleObstruction
section
namespace Lax762056.CycleObstruction

open AsteroidalCycles ColumnGraph Grid InducedMinors

axiom asteroidalCycles_obstruction (R W : Type*) (c : ℕ) (H : SimpleGraph W)
    (hH : HasAsteroidalCycleTriple H) :
  ¬ IsInducedMinor H (columnGraph R c)

end Lax762056.CycleObstruction
end
