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

/-- An unordered pair crosses the vertex set `S`. -/
def Crosses {V : Type u} [DecidableEq V]
    (S : Finset V) (e : Sym2 V) : Prop :=
  ∃ x y : V, e = s(x, y) ∧
    ((x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S))

namespace MatchingRound

end MatchingRound

namespace CutMatchingTranscript

end CutMatchingTranscript

end Lax17.Expansion
end
