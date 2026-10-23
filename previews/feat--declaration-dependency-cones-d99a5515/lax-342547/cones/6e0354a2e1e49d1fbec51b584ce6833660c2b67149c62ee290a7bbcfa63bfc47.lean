-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- Lax342547.RestrictionRank
section
namespace Lax342547.RestrictionRank

axiom bilinear_restriction_rank {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (S : Submodule K V) :
    Module.finrank K (LinearMap.range B) ≤ Module.finrank K (LinearMap.range (B.restrict S)) +
      2 * (Module.finrank K V - Module.finrank K S)

end Lax342547.RestrictionRank
end
