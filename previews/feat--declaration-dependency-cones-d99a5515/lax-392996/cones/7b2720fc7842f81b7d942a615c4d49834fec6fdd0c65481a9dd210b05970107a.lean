-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
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

-- Lax392996.WhyProvenance
section
namespace Lax392996.WhyProvenance

open Lax392996.SemiringsWithMonus

variable {α : Type}

/-- Why-provenance over `α`: a family of sets of witnesses. -/
@[ext]
structure Why (α: Type) where
  carrier : Set (Set α)

instance instCoeWhySet : Coe (Why α) (Set (Set α)) := ⟨Why.carrier⟩

instance instZeroWhy : Zero (Why α) where
  zero := ⟨∅⟩

instance instAddWhy : Add (Why α) where
  add a b := ⟨a ∪ b⟩

/-- Pairwise union of witnesses, the multiplication of `Why α`. -/
def why_mul (a b: Why α) : Why α :=
  ⟨{ z : Set α | ∃ x y : Set α, x ∈ a.carrier ∧ y ∈ b.carrier ∧ z = x ∪ y}⟩

instance instCommSemiringWhy : CommSemiring (Why α) where
  one := ⟨{∅}⟩
  mul := why_mul

  add_assoc := by
    intro a b c
    simp [HAdd.hAdd, Add.add]
    exact Set.union_assoc _ _ _

  zero_add := by
    intro a
    show ⟨(⟨∅⟩ : Why α).carrier ∪ a.carrier⟩ = a
    simp

  add_zero := by
    intro a
    show ⟨a.carrier ∪ (⟨∅⟩ : Why α).carrier⟩ = a
    simp

  add_comm := by
    intro a b
    simp [HAdd.hAdd, Add.add]
    exact Set.union_comm _ _

  mul_assoc := by
    intro a b c
    unfold why_mul
    ext w
    simp [HMul.hMul]
    apply Iff.intro
    . intro h
      obtain ⟨xa, xb, h₁, h₂⟩ := h
      obtain ⟨hxa, hxb⟩ := h₁
      obtain ⟨xc, hxc, hw⟩ := h₂
      use xa, hxa, xb, xc
      constructor
      . use hxb, hxc
      . simp[hw, Set.union_assoc]

    . intro h
      obtain ⟨xa, hxa, xb, xc, hxbc, hw⟩ := h
      use xa, xb
      constructor
      . use hxa, hxbc.1
      . use xc, hxbc.2
        simp[hw, Set.union_assoc]

  one_mul := by
    intro a
    show why_mul (⟨{∅}⟩: Why α) a = a
    unfold why_mul
    simp

  mul_one := by
    intro a
    show why_mul a (⟨{∅}⟩: Why α) = a
    unfold why_mul
    simp

  zero_mul := by
    intro a
    show why_mul (⟨∅⟩: Why α) a = (⟨∅⟩: Why α)
    unfold why_mul
    simp

  mul_zero := by
    intro a
    show why_mul a (⟨∅⟩: Why α) = (⟨∅⟩: Why α)
    unfold why_mul
    simp

  mul_comm := by
    intro a b
    show why_mul a b = why_mul b a
    unfold why_mul
    ext z
    simp
    apply Iff.intro
    . intro h
      obtain ⟨x, hx, y, hy, hz⟩ := h
      use y, hy, x, hx
      simp[hz, Set.union_comm]
    . intro h
      obtain ⟨y, hy, x, hx, hz⟩ := h
      use x, hx, y, hy
      simp[hz, Set.union_comm]

  left_distrib := by
    intro a b c
    show why_mul a ⟨b ∪ c⟩ = ⟨(why_mul a b) ∪ (why_mul a c)⟩
    unfold why_mul
    ext z
    simp
    apply Iff.intro
    . intro h
      obtain ⟨x, hx, y, hy, hz⟩ := h
      cases hy with
      | inl hy' =>
        apply Or.inl
        use x, hx, y, hy'
      | inr hy' =>
        apply Or.inr
        use x, hx, y, hy'
    . intro h
      cases h with
      | inl h' =>
        obtain ⟨x, hx, y, hy, hz⟩ := h'
        use x, hx, y
        simp[hy, hz]
      | inr h' =>
        obtain ⟨x, hx, y, hy, hz⟩ := h'
        use x, hx, y
        simp[hy, hz]

  right_distrib := by
    intro a b c
    show why_mul ⟨a ∪ b⟩ c = ⟨(why_mul a c) ∪ (why_mul b c)⟩
    unfold why_mul
    simp
    ext z
    simp
    apply Iff.intro
    . intro h
      obtain ⟨x, hx, y, hy, hz⟩ := h
      cases hx with
      | inl hx' =>
        apply Or.inl
        use x, hx', y, hy
      | inr hx' =>
        apply Or.inr
        use x, hx', y, hy
    . intro h
      cases h with
      | inl h' =>
        obtain ⟨x, hx, y, hy, hz⟩ := h'
        use x
        simp[hx]
        use y
      | inr h' =>
        obtain ⟨x, hx, y, hy, hz⟩ := h'
        use x
        simp[hx]
        use y

  nsmul := nsmulRec

/-- The support indicator: `𝟘` on the empty family, `𝟙` on any nonempty
one. This is the `δ` of `Why α`. -/
def Why.deltaInd (a : Why α) : Why α :=
  ⟨{s | s = ∅ ∧ a.carrier.Nonempty}⟩

/-- Why-provenance is a semiring with monus: `∖` is set difference on the outer
level, `2^(2^X)` ordered by inclusion. -/
instance instSemiringWithMonusWhy : SemiringWithMonus (Why α) where
  le a b := a.carrier ⊆ b.carrier
  le_refl := by simp
  le_trans := by
    intro a b c ha hb x hx
    exact hb (ha hx)

  le_antisymm := by
    intro a b ha hb
    ext x
    apply Iff.intro
    . exact fun a ↦ ha (hb (ha a))
    . exact fun a ↦ hb (ha (hb a))

  add_le_add_left := by
    simp[HAdd.hAdd,Add.add]
    intro a b hab c x hx
    simp
    apply Or.inl
    exact hab hx

  add_le_add_right := by
    simp[HAdd.hAdd,Add.add]
    intro a b hab c x hx
    simp
    apply Or.inr
    exact hab hx

  exists_add_of_le := by
    intro a b hab
    simp[HAdd.hAdd,Add.add]
    use ⟨b.carrier \ a.carrier⟩
    ext x
    simp
    intro hx
    exact hab hx

  le_self_add := by
    intro a b x hx
    simp[HAdd.hAdd,Add.add]
    apply Or.inl
    exact hx

  le_add_self := by
    intro a b x hx
    simp[HAdd.hAdd,Add.add]
    apply Or.inr
    exact hx

  sub a b := ⟨a.carrier \ b.carrier⟩
  monus_spec := by
    intro a b c
    simp[HAdd.hAdd,Add.add]
    show (⟨a.carrier \ b.carrier⟩: Why α).carrier ⊆ c.carrier ↔ a.carrier ⊆ b.carrier ∪ c.carrier
    apply Iff.intro
    . intro h x hx
      by_cases hx' : x ∈ b.carrier
      . apply Or.inl
        exact hx'
      . apply Or.inr
        have h' : x ∈ a.carrier \ b.carrier := by simp[hx, hx']
        exact h h'
    . intro h x hx
      simp at hx
      obtain ⟨ha, hb⟩ := hx
      have h' : x ∈ b.carrier ∪ c.carrier := h ha
      simp at h'
      tauto

  delta := Why.deltaInd
  delta_zero := by
    ext z
    show z ∈ {s | s = ∅ ∧ (∅ : Set (Set α)).Nonempty} ↔ z ∈ (∅ : Set (Set α))
    simp
  delta_natCast_pos := by
    have hidem : ∀ a : Why α, a + a = a := fun a => by simp [(· + ·), Add.add]
    have hone : (1 : Why α) ≠ 0 := by
      intro h
      have := congrArg Why.carrier h
      exact Set.singleton_ne_empty (∅ : Set α) this
    have hcast : ∀ {n : ℕ}, 0 < n → (n : Why α) = 1 := by
      intro n hn
      induction n with
      | zero => omega
      | succ m ih =>
        rcases Nat.eq_zero_or_pos m with hm | hm
        · rw [hm]; simp
        · rw [Nat.cast_succ, ih hm, hidem 1]
    have hne : ∀ {a : Why α}, a ≠ 0 → Why.deltaInd a = 1 := by
      intro a h
      have hnonempty : a.carrier.Nonempty := by
        rcases Set.eq_empty_or_nonempty a.carrier with he | hne
        · exact absurd (by ext z; rw [he]; exact Iff.rfl) h
        · exact hne
      ext z
      show z ∈ {s | s = ∅ ∧ a.carrier.Nonempty} ↔ z ∈ ({∅} : Set (Set α))
      simp [hnonempty]
    intro n hn
    rw [hcast hn, hne hone]
  delta_absorb := fun a b => by
    have hzsf : ∀ {a b : Why α}, a + b = 0 → a = 0 := by
      intro a b h
      have hc : a.carrier ∪ b.carrier = (∅ : Set (Set α)) :=
        congrArg Why.carrier h
      have hx : a.carrier = ∅ := by
        ext w
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hw
        have hmem : w ∈ a.carrier ∪ b.carrier := Set.mem_union_left _ hw
        rw [hc] at hmem
        exact hmem
      ext z
      rw [hx]
      exact Iff.rfl
    have hne : ∀ {a : Why α}, a ≠ 0 → Why.deltaInd a = 1 := by
      intro a h
      have hnonempty : a.carrier.Nonempty := by
        rcases Set.eq_empty_or_nonempty a.carrier with he | hne
        · exact absurd (by ext z; rw [he]; exact Iff.rfl) h
        · exact hne
      ext z
      show z ∈ {s | s = ∅ ∧ a.carrier.Nonempty} ↔ z ∈ ({∅} : Set (Set α))
      simp [hnonempty]
    by_cases ha : a = 0
    · rw [ha, zero_mul]
    · have habne : a + b ≠ 0 := fun h => ha (hzsf h)
      show a * Why.deltaInd (a + b) = a
      rw [hne habne, mul_one]

end Lax392996.WhyProvenance
end
