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
namespace Lax17.Expansion.BalancedSeparator
end Lax17.Expansion.BalancedSeparator

namespace Lax17.Expansion

universe u

open Lax17.Degree

/-- One cut-matching round: a bisection and a perfect matching from its left
half to its right half. -/
structure MatchingRound (V : Type u) [Fintype V] [DecidableEq V] where
  left : Finset V
  right : Finset V
  sides_disjoint : Disjoint left right
  sides_equipotent : left.card = right.card
  sides_cover : left ∪ right = Finset.univ
  partner : {x : V // x ∈ left} ≃ {x : V // x ∈ right}

namespace MatchingRound

end MatchingRound

namespace CutMatchingTranscript

end CutMatchingTranscript

end Lax17.Expansion
end
