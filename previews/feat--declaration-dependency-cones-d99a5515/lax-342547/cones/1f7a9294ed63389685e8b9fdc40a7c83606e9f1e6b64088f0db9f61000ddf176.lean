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

def Compatible (J D : Submodule Binary V) (J' D' : Submodule Binary W)
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary) : Prop :=
  ∀ v : J, ∀ w : J', v.val ∈ D ∨ w.val ∈ D' → T v w = A v.val w.val

def ExtendsFrozen (D Keys : Submodule Binary V) (D' Keys' : Submodule Binary W)
    (A B : V →ₗ[Binary] W →ₗ[Binary] Binary) : Prop :=
  ∀ v w, v ∈ D ⊔ Keys ∨ w ∈ D' ⊔ Keys' → B v w = A v w

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

axiom bounded_baseline [FiniteDimensional Binary V] [FiniteDimensional Binary W]
    (J D Keys U : Submodule Binary V) (J' D' Keys' U' : Submodule Binary W)
    (hD : D ≤ J) (hD' : D' ≤ J') (hKeys : Disjoint J Keys) (hKeys' : Disjoint J' Keys')
    (hspan : J ⊔ U = ⊤) (hKeyPrimal : Keys ≤ U)
    (hspan' : J' ⊔ U' = ⊤) (hKeyPrimal' : Keys' ≤ U')
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary)
    (h : Compatible J D J' D' A T) :
    ∃ B : V →ₗ[Binary] W →ₗ[Binary] Binary,
      ExtendsFrozen D Keys D' Keys' A B ∧ (∀ v : J, ∀ w : J', B v.val w.val = T v w) ∧
      (∀ q : C →ₗ[Binary] J',
        Module.finrank Binary (LinearMap.range (B.compl₁₂ U.subtype (J'.subtype.comp q))) ≤
          Module.finrank Binary ↥(J ⊓ U) + Module.finrank Binary Keys + Module.finrank Binary D') ∧
      ∀ q : C →ₗ[Binary] J,
        Module.finrank Binary (LinearMap.range (B.flip.compl₁₂ U'.subtype (J.subtype.comp q))) ≤
          Module.finrank Binary ↥(J' ⊓ U') + Module.finrank Binary Keys' + Module.finrank Binary D

end Lax342547.BaselineRank
end
