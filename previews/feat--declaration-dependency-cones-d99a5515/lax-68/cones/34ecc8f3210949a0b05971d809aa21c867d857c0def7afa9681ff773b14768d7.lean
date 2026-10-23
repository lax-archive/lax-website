-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic

-- Lax68.SeriesParallel
section
namespace Lax68.SeriesParallel.TwoTerminal
end Lax68.SeriesParallel.TwoTerminal

set_option autoImplicit false

namespace Lax68.SeriesParallel

def edgeGraph {V : Type*} (s t : V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v =>
    (u = s ∧ v = t) ∨
    (u = t ∧ v = s)

end Lax68.SeriesParallel
end
