-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.SetTheory.Cardinal.Finite

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

-- Lax871432.HomomorphismCounts
section
namespace Lax871432.HomomorphismCounts

/-- $\hom(F, G)$, the number of homomorphisms from `F` to `G`. -/
noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card (F →g G)

end Lax871432.HomomorphismCounts
end

-- Lax871432.CategoricalProductCounts
section
open Lax871432.GraphProducts Lax871432.HomomorphismCounts

open scoped Lax871432.GraphProducts

namespace Lax871432.CategoricalProductCounts

/-- A homomorphism into a categorical product is a pair of homomorphisms into its two
factors. -/
axiom homCount_catProd_right {U V W : Type*} [Finite U] [Finite V] [Finite W]
    (F : SimpleGraph U) (G₁ : SimpleGraph V) (G₂ : SimpleGraph W) :
    homCount F (G₁ ×g G₂) = homCount F G₁ * homCount F G₂

end Lax871432.CategoricalProductCounts
end
