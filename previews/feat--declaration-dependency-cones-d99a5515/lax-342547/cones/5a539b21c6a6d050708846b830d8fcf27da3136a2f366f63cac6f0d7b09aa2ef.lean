-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Bilinear

-- Lax342547.FlatRank
section
namespace Lax342547.FlatRank

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

noncomputable def quotientPairing (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    LinearMap.BilinForm K (V ⧸ B.ker) :=
  LinearMap.IsRefl.liftQ₂ B B.ker hB.isRefl le_rfl

axiom exists_commuting_idempotents [FiniteDimensional K V] {ι : Type}
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (U : Submodule K V)
    (hflat : Module.finrank K (LinearMap.range (B.restrict U)) =
      Module.finrank K (LinearMap.range B))
    (shift : ι → U →ₗ[K] V)
    (hadj : ∀ a (x y : U), B (shift a x) y = B x (shift a y))
    (hidem : ∀ a (x y : U), B (shift a x) (shift a y) = B (shift a x) y)
    (hcomm : ∀ a c (x y : U), B (shift a x) (shift c y) = B (shift c x) (shift a y)) :
    ∃ M : ι → Module.End K (V ⧸ B.ker),
      (∀ a (x : U), M a (B.ker.mkQ x) = B.ker.mkQ (shift a x)) ∧
      (∀ a x y, quotientPairing B hB (M a x) y = quotientPairing B hB x (M a y)) ∧
      (∀ a, M a * M a = M a) ∧ ∀ a c, M a * M c = M c * M a

end Lax342547.FlatRank
end
