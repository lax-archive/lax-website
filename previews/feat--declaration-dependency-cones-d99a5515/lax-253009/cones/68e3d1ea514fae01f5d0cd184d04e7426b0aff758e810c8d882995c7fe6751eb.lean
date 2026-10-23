-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax253009.FiniteProbability
section
namespace Lax253009.FiniteProbability

open scoped BigOperators

noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax253009.FiniteProbability
end

-- Lax253009.LongCode
section
namespace Lax253009.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

abbrev Table (w : ℕ) := Coordinate w → Bool

def compose {w s : ℕ} (f : Fin s → Coordinate w) (B : Word s → Bool) : Coordinate w :=
  fun x ↦ B (fun i ↦ f i x)

def Accepts {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w) : Prop :=
  ∀ B : Word s → Bool, A (compose f B) = B (fun i ↦ A (f i))

def LooksLike {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w) (x : Word w) : Prop :=
  (∀ i, A (f i) = f i x) ∧
  (∀ B : Word s → Bool, A (compose f B) = compose f B x)

def AgreesOn {w : ℕ} (h g g' : Coordinate w) : Prop :=
  ∀ x, h x = true → g x = g' x

def Queried {w s : ℕ} (f : Fin s → Coordinate w) (g : Coordinate w) : Prop :=
  (∃ i, g = f i) ∨ ∃ B : Word s → Bool, g = compose f B

def AcceptsWithCondition {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Coordinate w) : Prop :=
  Accepts A f ∧ ∀ g, Queried f g → ∀ g', AgreesOn h g g' → A g = A g'

end Lax253009.LongCode
end

-- Lax253009.CNASoundness
section
namespace Lax253009.CNASoundness

open LongCode FiniteProbability

def BadWithCondition {w s : ℕ} (A : Table w) (S : Finset (Word w))
    (h : Coordinate w) (f : Fin s → Coordinate w) : Prop :=
  AcceptsWithCondition A f h ∧ ¬ ∃ x ∈ S, h x = true ∧ LooksLike A f x

axiom with_side_conditions (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 0 < k) :
  ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
    ∀ A : Table w, ∃ S : Finset (Word w),
      (S.card : ℝ) ≤ Real.rpow 2 (ε * (s : ℝ)) ∧
      ∀ h : Coordinate w,
        probability (BadWithCondition (s := s) A S h) ≤ Real.rpow 2 (-(k : ℝ) * (s : ℝ))

end Lax253009.CNASoundness
end
