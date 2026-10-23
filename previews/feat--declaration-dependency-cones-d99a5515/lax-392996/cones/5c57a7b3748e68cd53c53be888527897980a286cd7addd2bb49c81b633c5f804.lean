-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder

-- Lax392996.SemiringsWithMonus
section
namespace Lax392996
end Lax392996

namespace Lax392996.SemiringsWithMonus
end Lax392996.SemiringsWithMonus

namespace Lax392996.SemiringsWithMonus.HasAltLinearOrder
end Lax392996.SemiringsWithMonus.HasAltLinearOrder

namespace Lax392996.SemiringsWithMonus.SemiringWithMonus
end Lax392996.SemiringsWithMonus.SemiringWithMonus
end

-- Lax392996.BooleanFunctions
section
namespace Lax392996.BooleanFunctions

open Lax392996.SemiringsWithMonus

variable {X : Type}

/-- The type of Boolean functions over Boolean assignments to `X`:
`(X → Bool) → Bool` with pointwise operations. -/
def BoolFunc (X : Type) := (X → Bool) → Bool

instance instZeroBoolFunc : Zero (BoolFunc X) := ⟨λ _ ↦ False⟩

instance instAddBoolFunc : Add  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) || (f₂ ν)⟩

instance instOneBoolFunc : One  (BoolFunc X) := ⟨λ _ ↦ True⟩

instance instMulBoolFunc : Mul  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) && (f₂ ν)⟩

instance instCommSemiringBoolFunc : CommSemiring (BoolFunc X) where
  add_assoc := by
    intro a b c
    simp[(· + ·),Add.add]
    apply funext
    intro x
    exact Bool.or_assoc _ _ _

  add_comm := by
    intro a b
    simp[(· + ·),Add.add]
    apply funext
    intro x
    exact Bool.or_comm _ _

  zero_add := by tauto

  add_zero := by
    simp[(· + ·),Add.add]
    intro a
    apply funext
    simp
    tauto

  nsmul := nsmulRec

  left_distrib := by
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    intro a b c
    apply funext
    intro x
    exact Bool.and_or_distrib_left _ _ _

  right_distrib := by
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    intro a b c
    apply funext
    intro x
    exact Bool.and_or_distrib_right _ _ _

  zero_mul := by tauto

  mul_zero := by
    simp[(· * ·),Mul.mul]
    intro a
    apply funext
    simp
    tauto

  mul_assoc := by
    intro a b c
    simp[(· * ·),Mul.mul]
    apply funext
    intro x
    exact Bool.and_assoc _ _ _

  mul_comm := by
    intro a b
    simp[(· * ·),Mul.mul]
    apply funext
    intro x
    exact Bool.and_comm _ _

  one_mul := by tauto

  mul_one := by
    simp[(· * ·),Mul.mul]
    intro a
    apply funext
    simp
    tauto

end Lax392996.BooleanFunctions
end
