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

def Hole (D : HoleData Ω X V) (i j : Ω) : Prop :=
  ∃ x y : X, D.U i x = D.U j y ∧
    (∀ z, D.u j (D.U i z) = D.a z + D.T x z) ∧
    (∀ z, D.u i (D.U j z) = D.a z + D.T y z) ∧
    D.a x + D.a y = 1

end Lax342547.HoleRelation
end

-- Lax342547.HoleTriangleFree
section
namespace Lax342547.HoleTriangleFree

open HoleRelation

universe u v w

axiom hole_properties
    {Ω : Type u} {X : Type v} {V : Type w}
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup V] [Module (ZMod 2) V]
    (D : HoleData Ω X V) :
    (∀ ⦃i j⦄, Hole D i j → Hole D j i) ∧ (∀ i, ¬ Hole D i i) ∧
      ∀ i j k, Hole D i j → Hole D j k → ¬ Hole D k i

end Lax342547.HoleTriangleFree
end
