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

end Lax342547.FlatRank
end
