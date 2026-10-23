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
namespace Lax392996.SemiringsWithMonus.HasAltLinearOrder
end Lax392996.SemiringsWithMonus.HasAltLinearOrder

universe u

namespace Lax392996.SemiringsWithMonus

/-- A `SemiringWithMonus` is a naturally ordered semiring
with a monus operation that is compatible with the natural order.
The semiring is not required to be commutative.

In addition to monus, the class carries a `δ : α → α` operator subject
to three axioms (`delta_zero`, `delta_natCast_pos`, and
`delta_absorb`). This is the duplicate-eliminating support
operator used to interpret aggregation in the framework of
[Amsterdamer, Deutch & Tannen, *Provenance for aggregate queries*][amsterdamer2011aggregate]. -/
class SemiringWithMonus (α : Type)
  extends Semiring α, PartialOrder α, IsOrderedAddMonoid α, CanonicallyOrderedAdd α, Sub α where
  monus_spec : ∀ a b c : α, a - b ≤ c ↔ a ≤ b + c
  /-- Duplicate-eliminating support operator. Sends `0` to `0` and any
  positive integer iterate of `1` to `1`. -/
  delta : α → α
  /-- `δ` sends `0` to `0`. -/
  delta_zero : delta 0 = 0
  /-- `δ` sends every positive integer iterate of `1` (i.e., every
  positive natural-number cast) to `1`. -/
  delta_natCast_pos : ∀ {n : ℕ}, 0 < n → delta ((n : α)) = 1
  /-- A δ-guard is absorbed by any multiple of one of its summands:
  `a ⊗ δ(a ⊕ b) = a`. This is what makes a group-existence factor
  redundant next to any provenance that already contains an occurrence
  of the group: `δ` acts as “the group exists” and nothing more. -/
  delta_absorb : ∀ (a b : α), a * delta (a + b) = a

end Lax392996.SemiringsWithMonus
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

instance instLEBoolFunc : LE   (BoolFunc X) := ⟨λ f₁ f₂ ↦ ∀ ν : X → Bool, (f₁ ν) ≤ (f₂ ν)⟩

instance instSubBoolFunc : Sub  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) && !(f₂ ν)⟩

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

/-- `BoolFunc X` is a commutative m-semiring with pointwise `||` as addition,
pointwise `&&` as multiplication, and pointwise implication as natural order. -/
instance instSemiringWithMonusBoolFunc : SemiringWithMonus (BoolFunc X) where
  le_refl := by tauto

  le_trans := by tauto

  le_antisymm := by
    simp[(· ≤ ·)]
    intro a b hab hba
    apply funext
    intro ν
    exact Bool.le_antisymm (hab ν) (hba ν)

  le_self_add := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  le_add_self := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  add_le_add_left := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  exists_add_of_le := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    intro a b h
    use b
    apply funext
    intro x
    cases ha : a x
    . tauto
    . apply (h x) ha

  monus_spec := by
    intro a b c
    simp[(· + ·),Add.add,(· ≤ ·),(· - ·),Sub.sub]
    apply Iff.intro
    . intro h ν ha
      cases hb : b ν <;> simp
      . exact h ν ha hb
    . intro h ν ha hb
      have h' : b ν = true ∨ c ν = true := h ν ha
      simp[hb] at h'
      exact h'

  delta := id
  delta_zero := rfl
  delta_natCast_pos := by
    have hidem : ∀ a : BoolFunc X, a + a = a := fun a => funext fun ν => by
      show (a ν || a ν) = a ν
      simp
    have hcast : ∀ {n : ℕ}, 0 < n → (n : BoolFunc X) = 1 := by
      intro n hn
      induction n with
      | zero => omega
      | succ m ih =>
        rcases Nat.eq_zero_or_pos m with hm | hm
        · rw [hm]; simp
        · rw [Nat.cast_succ, ih hm, hidem 1]
    intro n hn
    exact hcast hn
  delta_absorb := fun a b => funext fun ν => by
    show (a ν && (a ν || b ν)) = a ν
    cases a ν <;> cases b ν <;> rfl

end Lax392996.BooleanFunctions
end
