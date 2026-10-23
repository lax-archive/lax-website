-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Paths

-- Lax881656.HamiltonianCycle
section
set_option autoImplicit false

namespace Lax881656.HamiltonianCycle

/-- A closed walk is a Hamiltonian cycle when it is a cycle and visits every
vertex of the graph. -/
def IsHamiltonianCycle {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {v : V} (cycle : G.Walk v v) : Prop :=
  cycle.IsCycle ∧ ∀ w : V, w ∈ cycle.support

/-- A graph has a Hamiltonian cycle when it contains a spanning cycle. -/
def HasHamiltonianCycle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∃ cycle : G.Walk v v, IsHamiltonianCycle cycle

end Lax881656.HamiltonianCycle
end
