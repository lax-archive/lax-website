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
namespace Lax68
end Lax68

namespace Lax68.GraphMinors
end Lax68.GraphMinors

namespace Lax68.GraphMinors.MinorModel
end Lax68.GraphMinors.MinorModel
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

/-- `𝓕` is *closed under taking summands* if both summands of a disjoint union in the class
are themselves in the class. -/
def IsSummandClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] (F₁ : SimpleGraph V) (F₂ : SimpleGraph W),
    𝓕.Mem (F₁ ⊕g F₂) → 𝓕.Mem F₁ ∧ 𝓕.Mem F₂

end Lax871432.ClosureProperties
end
