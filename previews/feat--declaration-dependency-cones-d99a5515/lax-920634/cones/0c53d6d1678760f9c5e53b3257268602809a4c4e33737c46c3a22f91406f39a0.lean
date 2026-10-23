-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic

-- Lax920634.EdgeExpansion
section
namespace Lax920634.EdgeExpansion

/-- Boundary edges oriented from the set to its complement, each counted once. -/
def edgeBoundary {V : Type} (G : SimpleGraph V) (S : Set V) : Set (V × V) :=
  {e | e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2}

/-- Every vertex set of size at most half the graph has at least `h` times
its size in boundary edges. -/
def HasEdgeExpansionAtLeast {V : Type} [Fintype V]
    (G : SimpleGraph V) (h : ℚ) : Prop :=
  ∀ S : Set V, 2 * S.ncard ≤ Fintype.card V →
    h * (S.ncard : ℚ) ≤ ((edgeBoundary G S).ncard : ℚ)

/-- Every vertex has at most three distinct neighbors. -/
def IsSubcubic {V : Type} [Finite V] (G : SimpleGraph V) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ 3

end Lax920634.EdgeExpansion
end

-- Lax920634.SeedSearch
section
namespace Lax920634.SeedSearch

open Function

/-- A fixed powering exponent sufficient for the lazy permutation seed. -/
def poweringExponent : ℕ := 5760000

/-- The fixed degree of the powered seed. -/
def seedDegree : ℕ := 120 ^ poweringExponent

end Lax920634.SeedSearch
end

-- Lax920634.SeedRotation
section
namespace Lax920634.SeedRotation
end Lax920634.SeedRotation

namespace Lax920634.SeedRotation.lazyRotation
end Lax920634.SeedRotation.lazyRotation

namespace Lax920634.SeedRotation.walkAt
end Lax920634.SeedRotation.walkAt

namespace Lax920634.SeedRotation.walkEnd
end Lax920634.SeedRotation.walkEnd
end

-- Lax920634.ZigZagConstruction
section
namespace Lax920634.ZigZagConstruction.rotation
end Lax920634.ZigZagConstruction.rotation

namespace Lax920634.ZigZagConstruction

open SeedSearch

/-- The fixed degree of each regular graph in the tower. -/
def degree : ℕ := seedDegree ^ 2

end Lax920634.ZigZagConstruction
end

-- Lax920634.ExpanderExistence
section
namespace Lax920634.ExpanderExistence

open ZigZagConstruction EdgeExpansion

/-- There are arbitrarily large finite simple subcubic expanders with one fixed constant. -/
axiom exists_subcubic_expander (lower : ℕ) :
  ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), lower ≤ n ∧
    IsSubcubic G ∧
    HasEdgeExpansionAtLeast G (1 / (8 * (degree : ℚ)))

end Lax920634.ExpanderExistence
end
