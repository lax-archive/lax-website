-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

-- Lax68.GraphMinors
section
set_option autoImplicit false

namespace Lax68.GraphMinors

structure MinorModel {W V : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  branchSet : W → Set V
  connected : ∀ w, (G.induce (branchSet w)).Connected
  disjoint :
    ∀ {u v}, u ≠ v →
      Disjoint (branchSet u) (branchSet v)
  adjacent :
    ∀ {u v}, H.Adj u v →
      ∃ x ∈ branchSet u, ∃ y ∈ branchSet v, G.Adj x y

def IsMinor {W V : Type*}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (MinorModel H G)

end Lax68.GraphMinors
end

-- Lax68.AcyclicMinors
section
set_option autoImplicit false

namespace Lax68.AcyclicMinors

/-- Taking a graph minor preserves acyclicity. -/
axiom acyclic_minor {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} :
  G.IsAcyclic → Lax68.GraphMinors.IsMinor H G → H.IsAcyclic

end Lax68.AcyclicMinors
end
