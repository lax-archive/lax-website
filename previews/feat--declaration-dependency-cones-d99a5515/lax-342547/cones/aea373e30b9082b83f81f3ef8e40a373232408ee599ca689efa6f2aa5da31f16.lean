-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Projection

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.FrozenBaselines
section
namespace Lax342547.FrozenBaselines
end Lax342547.FrozenBaselines

namespace Lax342547.FrozenBaselines.Splitting
end Lax342547.FrozenBaselines.Splitting
end

-- Lax342547.PrimalRetractions
section
namespace Lax342547.PrimalRetractions

open Lax342547.MomentSpace

axiom bounded_retraction {V : Type} [AddCommGroup V] [Module Binary V]
    [FiniteDimensional Binary V] (J Keys U : Submodule Binary V)
    (hspan : J ⊔ U = ⊤) (hKeys : Keys ≤ U) :
    ∃ p : V →ₗ[Binary] V,
      (∀ v, p v ∈ J ⊔ Keys) ∧ (∀ v ∈ J ⊔ Keys, p v = v) ∧
      (∀ v ∈ U, p v ∈ U) ∧
      Module.finrank Binary (LinearMap.range (p.comp U.subtype)) ≤
        Module.finrank Binary ↥(J ⊓ U) + Module.finrank Binary Keys

end Lax342547.PrimalRetractions
end
