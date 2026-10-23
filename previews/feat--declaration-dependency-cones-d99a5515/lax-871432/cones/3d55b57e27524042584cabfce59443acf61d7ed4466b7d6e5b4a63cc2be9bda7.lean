-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sum
import Mathlib.Order.SetNotation

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

-- Lax871432.Contractions
section
namespace Lax871432
end Lax871432

namespace Lax871432.Contractions
end Lax871432.Contractions

namespace Lax871432.Contractions.Contraction
end Lax871432.Contractions.Contraction
end

-- Lax871432.GraphClasses
section
namespace Lax871432.GraphClasses

/-- A class of finite simple graphs, given by an isomorphism-invariant predicate on the
finite simple graphs. -/
structure GraphClass where
  /-- The graphs of the class. -/
  Mem : ∀ {V : Type} [Finite V], SimpleGraph V → Prop
  /-- The class is invariant under isomorphism. -/
  mem_congr : ∀ {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V} {F' : SimpleGraph W},
    Nonempty (F ≃g F') → (Mem F ↔ Mem F')

end Lax871432.GraphClasses
end

-- Lax871432.ClosureProperties
section
open Lax871432.Contractions Lax871432.GraphClasses

namespace Lax871432.ClosureProperties

/-- `𝓕` is *minor-closed* if every minor of a member is a member. -/
def IsMinorClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V} (K : SimpleGraph W),
    Lax68.GraphMinors.IsMinor K F → 𝓕.Mem F → 𝓕.Mem K

end Lax871432.ClosureProperties
end
