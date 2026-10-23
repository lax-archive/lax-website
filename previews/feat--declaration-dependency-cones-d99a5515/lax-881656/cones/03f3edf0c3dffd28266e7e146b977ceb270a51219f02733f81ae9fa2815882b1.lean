-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

-- Lax881656.ThreeConnected
section
set_option autoImplicit false

namespace Lax881656.ThreeConnected

/-- A finite graph is 3-connected if deleting at most two vertices leaves a
connected graph, and the original graph has at least four vertices. -/
def IsThreeConnected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 2 →
      (G.induce {v : V | v ∉ S}).Connected

end Lax881656.ThreeConnected
end
