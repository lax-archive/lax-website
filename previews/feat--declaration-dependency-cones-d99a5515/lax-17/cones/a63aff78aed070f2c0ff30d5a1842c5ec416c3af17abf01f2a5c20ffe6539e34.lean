-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Rat.Defs

-- Lax17.Degree
section
namespace Lax17
end Lax17

namespace Lax17.Degree
end Lax17.Degree
end

-- Lax17.SpanningTreeRounding
section
namespace Lax17.SpanningTreeRounding.FeasiblePoint
end Lax17.SpanningTreeRounding.FeasiblePoint

namespace Lax17.SpanningTreeRounding

universe u

open Finset

/-- Both endpoints of an unordered pair lie in `S`. -/
def PairInside {V : Type u} [DecidableEq V]
    (S : Finset V) (e : Sym2 V) : Prop :=
  e.toFinset ⊆ S

end Lax17.SpanningTreeRounding
end
