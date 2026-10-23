-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- Lax342547.RestrictionRank
section
namespace Lax342547.RestrictionRank

axiom bilinear_pullback_rank {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (A : W →ₗ[K] V) :
    Module.finrank K (LinearMap.range B) ≤ Module.finrank K (LinearMap.range (B.comp A A)) +
      2 * (Module.finrank K V - Module.finrank K (LinearMap.range A))

end Lax342547.RestrictionRank
end
