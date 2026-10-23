-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib

-- Lax9.MergeWidth
section
namespace Lax9.MergeWidth

open scoped Classical

universe u

variable {V : Type u} [Fintype V]

/-- The **resolved ball** of radius $r$ around $v$ in a graph $H$:
the set of vertices reachable from $v$ by a walk of length at most $r$.
In the paper this is applied to the graph $(V, Rᵢ)$ of resolved pairs. -/
def resolvedBall (H : SimpleGraph V) (r : ℕ) (v : V) : Set V :=
  {u | ∃ w : H.Walk v u, w.length ≤ r}

namespace MergeSeq

variable {G : SimpleGraph V}

end MergeSeq

end Lax9.MergeWidth
end
