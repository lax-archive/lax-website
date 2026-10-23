-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite

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
