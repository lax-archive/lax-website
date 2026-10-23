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

axiom quotient_restriction_surjective [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (U : Submodule K V)
    (hflat : Module.finrank K (LinearMap.range (B.restrict U)) =
      Module.finrank K (LinearMap.range B)) :
    Function.Surjective (B.ker.mkQ.comp U.subtype)

end Lax342547.FlatRank
end
