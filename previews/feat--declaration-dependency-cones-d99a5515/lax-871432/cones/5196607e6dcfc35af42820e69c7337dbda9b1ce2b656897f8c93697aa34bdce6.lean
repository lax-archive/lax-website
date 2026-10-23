-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sum

-- Lax871432.GraphProducts
section
namespace Lax871432.GraphProducts

variable {α β : Type*}

/-- The *categorical product* of simple graphs: it relates `(a₁, b₁)` and `(a₂, b₂)` when `G`
relates `a₁` and `a₂` and `H` relates `b₁` and `b₂`. Contrast with `SimpleGraph.boxProd`. -/
def catProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

@[inherit_doc]
scoped infixl:70 " ×g " => catProd

end Lax871432.GraphProducts
end

-- Lax871432.IsomorphismRelaxations
section
namespace Lax871432.IsomorphismRelaxations

/-- A *graph isomorphism relaxation*: an equivalence relation on finite simple graphs which
relates any two isomorphic graphs, and is therefore invariant under isomorphism. -/
structure GraphIsoRelaxation where
  /-- The relation itself. -/
  Rel : ∀ ⦃V W : Type⦄ [Finite V] [Finite W], SimpleGraph V → SimpleGraph W → Prop
  /-- Isomorphic graphs are related; in particular the relation is reflexive. -/
  rel_of_iso : ∀ {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W},
    Nonempty (G ≃g H) → Rel G H
  /-- The relation is symmetric. -/
  symm : ∀ {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W},
    Rel G H → Rel H G
  /-- The relation is transitive. -/
  trans : ∀ {U V W : Type} [Finite U] [Finite V] [Finite W] {G : SimpleGraph U}
    {H : SimpleGraph V} {K : SimpleGraph W}, Rel G H → Rel H K → Rel G K

end Lax871432.IsomorphismRelaxations
end

-- Lax871432.PreservationProperties
section
open Lax871432.GraphProducts Lax871432.IsomorphismRelaxations

open scoped Lax871432.GraphProducts

namespace Lax871432.PreservationProperties

/-- `R` is *preserved under taking complements*. -/
def PreservedUnderCompl (R : GraphIsoRelaxation) : Prop :=
  ∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W),
    R.Rel G H → R.Rel Gᶜ Hᶜ

end Lax871432.PreservationProperties
end
