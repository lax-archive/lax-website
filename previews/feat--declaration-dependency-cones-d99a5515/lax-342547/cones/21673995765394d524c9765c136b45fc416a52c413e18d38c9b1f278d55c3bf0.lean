-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Dual.Lemmas
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

open Lax342547.MomentSpace

variable {V W : Type} [AddCommGroup V] [Module Binary V]
  [AddCommGroup W] [Module Binary W]

structure Splitting (J D Keys : Submodule Binary V) where
  frozen : V →ₗ[Binary] V
  table : V →ₗ[Binary] J
  frozen_fixed : ∀ v ∈ D ⊔ Keys, frozen v = v
  table_zero : ∀ v ∈ D ⊔ Keys, table v = 0
  frozen_table : ∀ v : J, frozen v.val ∈ D
  table_sum : ∀ v : J, frozen v.val + (table v.val).val = v.val

end Lax342547.FrozenBaselines
end

-- Lax342547.PrimalRetractions
section
namespace Lax342547.PrimalRetractions
end Lax342547.PrimalRetractions
end

-- Lax342547.BaselineRank
section
namespace Lax342547.BaselineRank

open Lax342547.MomentSpace Lax342547.FrozenBaselines

variable {V W C : Type} [AddCommGroup V] [Module Binary V]
  [AddCommGroup W] [Module Binary W] [AddCommGroup C] [Module Binary C]

def retracted {J D Keys : Submodule Binary V} (S : Splitting J D Keys)
    (hD : D ≤ J) (p : V →ₗ[Binary] V) (hfix : ∀ v ∈ J ⊔ Keys, p v = v) :
    Splitting J D Keys where
  frozen := S.frozen.comp p
  table := S.table.comp p
  frozen_fixed v hv := by
    rw [LinearMap.comp_apply, hfix v ((sup_le_sup hD le_rfl) hv)]
    exact S.frozen_fixed v hv
  table_zero v hv := by
    rw [LinearMap.comp_apply, hfix v ((sup_le_sup hD le_rfl) hv)]
    exact S.table_zero v hv
  frozen_table v := by
    rw [LinearMap.comp_apply, hfix v.val ((show J ≤ J ⊔ Keys from le_sup_left) v.property)]
    exact S.frozen_table v
  table_sum v := by
    simp only [LinearMap.comp_apply, hfix v.val ((show J ≤ J ⊔ Keys from le_sup_left) v.property)]
    exact S.table_sum v

end Lax342547.BaselineRank
end
