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
namespace Lax871432.Contractions

/-- A presentation of `K` as the graph obtained from `F` by contracting the edges inside the
classes of a partition of `V(F)` into connected parts. -/
structure Contraction {V W : Type*} (K : SimpleGraph W) (F : SimpleGraph V) where
  /-- The vertex of `K` a vertex of `F` is contracted to. -/
  proj : V → W
  /-- Each class induces a connected — in particular nonempty — subgraph of `F`. -/
  connected : ∀ w, (F.induce {v | proj v = w}).Connected
  /-- Distinct classes are adjacent in `K` exactly when `F` joins them. -/
  adj_iff : ∀ a b, K.Adj a b ↔ a ≠ b ∧ ∃ x y, F.Adj x y ∧ proj x = a ∧ proj y = b

/-- `K` is *obtained from `F` by contracting edges*. -/
def IsContraction {V W : Type*} (K : SimpleGraph W) (F : SimpleGraph V) : Prop :=
  Nonempty (Contraction K F)

end Lax871432.Contractions
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

/-- `𝓕` is *closed under contracting edges* if every quotient of a member by a partition into
connected parts is a member. -/
def IsContractionClosed (𝓕 : GraphClass) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] {F : SimpleGraph V} (K : SimpleGraph W),
    IsContraction K F → 𝓕.Mem F → 𝓕.Mem K

end Lax871432.ClosureProperties
end
