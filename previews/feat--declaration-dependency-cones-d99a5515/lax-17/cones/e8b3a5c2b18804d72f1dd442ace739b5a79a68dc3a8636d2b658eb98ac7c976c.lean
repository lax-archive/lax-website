-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Nat.Log

-- Lax17.Degree
section
namespace Lax17
end Lax17

namespace Lax17.Degree
end Lax17.Degree
end

-- Lax17.Expansion
section
namespace Lax17.Expansion

universe u

open Lax17.Degree

/-- A balanced vertex separator `A ∪ B ∪ S = V`, oriented so that `A` is
the smaller side and both large sides have size at most two thirds of the
graph. -/
structure BalancedSeparator {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B S : Finset V) : Prop where
  cover : A ∪ B ∪ S = Finset.univ
  left_right_disjoint : Disjoint A B
  left_separator_disjoint : Disjoint A S
  right_separator_disjoint : Disjoint B S
  left_card_le_right_card : A.card ≤ B.card
  right_balanced : 3 * B.card ≤ 2 * Fintype.card V
  no_edge_left_right :
    ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ¬ G.Adj a b

/-- Every balanced separator has size at least `|V| / d`, expressed without
division. -/
def NoSmallBalancedSeparator
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ ⦃A B S : Finset V⦄, BalancedSeparator G A B S →
    Fintype.card V ≤ d * S.card

namespace MatchingRound

end MatchingRound

namespace CutMatchingTranscript

end CutMatchingTranscript

end Lax17.Expansion
end

-- Lax17.Grid
section
namespace Lax17.Grid

/-- The canonical `g × g` square grid. -/
def squareGrid (g : ℕ) : SimpleGraph (Fin g × Fin g) :=
  SimpleGraph.pathGraph g □ SimpleGraph.pathGraph g

end Lax17.Grid
end

-- Lax17.Minor
section
namespace Lax17.Minor

universe u v

/-- Branch-set data witnessing that `H` is a minor of `G`. -/
structure Model {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set representing each vertex of `H`. -/
  branchSet : W → Set V
  /-- Every branch set is nonempty. -/
  branch_nonempty : ∀ w : W, (branchSet w).Nonempty
  /-- Every branch set induces a connected graph in `G`. -/
  branch_connected :
    ∀ w : W, (G.induce (branchSet w)).Connected
  /-- Branch sets representing distinct vertices are disjoint. -/
  branch_disjoint :
    ∀ ⦃x y : W⦄, x ≠ y → Disjoint (branchSet x) (branchSet y)
  /-- Every edge of `H` is represented by an edge between branch sets. -/
  adjacent :
    ∀ ⦃x y : W⦄, H.Adj x y →
      ∃ a ∈ branchSet x, ∃ b ∈ branchSet y, G.Adj a b

/-- `H` is a graph minor of `G`. -/
def IsMinor {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (Model H G)

end Lax17.Minor
end

-- Lax17.GridMinor
section
namespace Lax17.GridMinor

universe u

/-- `G` contains the `g × g` square grid as a minor. -/
def ContainsGridMinor {V : Type u} (G : SimpleGraph V) (g : ℕ) : Prop :=
  Lax17.Minor.IsMinor (Lax17.Grid.squareGrid g) G

end Lax17.GridMinor
end

-- Lax17.ExpanderGrid
section
namespace Lax17.ExpanderGrid

universe u

/-- The expander-to-grid handoff in the no-small-balanced-separator form. -/
axiom expanderContainsGrid :
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d g : ℕ),
      2 ≤ Fintype.card V →
        Lax17.Expansion.NoSmallBalancedSeparator G d →
          ((3 * (d + 1) * (15 * (d + 1))) * 8) *
              (5 * g ^ 2) * Nat.log 2 (Fintype.card V) ≤
                Fintype.card V →
            Lax17.GridMinor.ContainsGridMinor G g

end Lax17.ExpanderGrid
end
