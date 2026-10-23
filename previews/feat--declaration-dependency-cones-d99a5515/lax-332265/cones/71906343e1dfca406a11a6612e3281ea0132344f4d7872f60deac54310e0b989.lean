-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.Basic

-- Lax332265.SixColorable
section
namespace Lax332265.SixColorable

/-- A graph admits a proper vertex colouring with the six colours in `Fin 6`. -/
def IsSixColorable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ colour : V → Fin 6,
    ∀ ⦃u v : V⦄, G.Adj u v → colour u ≠ colour v

end Lax332265.SixColorable
end

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

-- Lax332265.HadwigerT7
section
namespace Lax332265.HadwigerT7

/-- Hadwiger's conjecture at `t = 7`: excluding a `K₇` minor guarantees a
proper colouring with six colours. -/
axiom sixColorable_of_no_K7_minor :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ¬ Lax68.GraphMinors.IsMinor
        (SimpleGraph.completeGraph (Fin 7)) G →
      Lax332265.SixColorable.IsSixColorable G

end Lax332265.HadwigerT7
end
