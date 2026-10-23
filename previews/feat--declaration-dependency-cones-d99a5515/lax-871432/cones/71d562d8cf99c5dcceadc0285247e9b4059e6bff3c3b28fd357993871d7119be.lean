-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.SetTheory.Cardinal.Finite

-- Lax871432.GraphFamilies
section
namespace Lax871432
end Lax871432

namespace Lax871432.GraphFamilies
end Lax871432.GraphFamilies

namespace Lax871432.GraphFamilies.GraphFamily
end Lax871432.GraphFamilies.GraphFamily
end

-- Lax871432.HomomorphismCounts
section
namespace Lax871432.HomomorphismCounts

/-- $\hom(F, G)$, the number of homomorphisms from `F` to `G`. -/
noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card (F →g G)

end Lax871432.HomomorphismCounts
end

-- Lax871432.LovaszTheorem
section
open Lax871432.GraphFamilies Lax871432.HomomorphismCounts

namespace Lax871432.LovaszTheorem

variable {n : ℕ} {ι : Type*}

/-- **Lovász's theorem.** Finite graphs with equal homomorphism counts from every graph are
isomorphic, and conversely. -/
axiom nonempty_iso_iff_forall_homCount_eq {V W : Type} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (∀ (m : ℕ) (K : SimpleGraph (Fin m)), homCount K G = homCount K H) ↔ Nonempty (G ≃g H)

end Lax871432.LovaszTheorem
end
