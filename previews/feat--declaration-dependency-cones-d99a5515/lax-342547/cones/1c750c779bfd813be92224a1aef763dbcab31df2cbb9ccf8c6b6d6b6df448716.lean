-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic

-- Lax342547.HoleRelation
section
namespace Lax342547.HoleRelation

universe u v w

structure HoleData (Ω : Type u) (X : Type v) (V : Type w)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup V] [Module (ZMod 2) V] where
  a : X →ₗ[ZMod 2] ZMod 2
  T : LinearMap.BilinForm (ZMod 2) X
  symmetric : ∀ x y, T x y = T y x
  U : Ω → X →ₗ[ZMod 2] V
  injective : ∀ i, Function.Injective (U i)
  u : Ω → V →ₗ[ZMod 2] ZMod 2

variable {Ω : Type u} {X : Type v} {V : Type w}

variable [AddCommGroup X] [Module (ZMod 2) X]

variable [AddCommGroup V] [Module (ZMod 2) V]

end Lax342547.HoleRelation
end
