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

def baseline {J D Keys : Submodule Binary V} {J' D' Keys' : Submodule Binary W}
    (S : Splitting J D Keys) (S' : Splitting J' D' Keys')
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary) :
    V →ₗ[Binary] W →ₗ[Binary] Binary :=
  A.compl₁₂ S.frozen LinearMap.id + A.compl₁₂ LinearMap.id S'.frozen -
    A.compl₁₂ S.frozen S'.frozen + T.compl₁₂ S.table S'.table

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

axiom channel_rank [FiniteDimensional Binary V] [FiniteDimensional Binary W]
    (J D Keys U : Submodule Binary V) (J' D' Keys' : Submodule Binary W)
    (hD : D ≤ J) (S : Splitting J D Keys) (S' : Splitting J' D' Keys')
    (p : V →ₗ[Binary] V) (hfix : ∀ v ∈ J ⊔ Keys, p v = v)
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary)
    (q : C →ₗ[Binary] J') :
    Module.finrank Binary (LinearMap.range
      ((baseline (retracted S hD p hfix) S' A T).compl₁₂ U.subtype (J'.subtype.comp q))) ≤
      Module.finrank Binary (LinearMap.range (p.comp U.subtype)) + Module.finrank Binary D'

end Lax342547.BaselineRank
end
