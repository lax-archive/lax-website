-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
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

end Lax253009.CNASoundness
end

-- Lax253009.ManyTableConsistency
section
namespace Lax253009.ManyTableConsistency
end Lax253009.ManyTableConsistency
end

-- Lax253009.FAFTest
section
namespace Lax253009.FAFTest

open LongCode FiniteProbability CNASoundness

noncomputable def condition {Ω : Type} {u w q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (R : Table u) (ω : Ω) (g : Fin q → Coordinate u) : Coordinate w :=
  fun y ↦ valid ω y && decide (∀ j, g j (ρ ω y) = R (g j))

def Accepts {Ω : Type} {u w n s q : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (R : Table u) (A : Ω → Table w)
    (ω : Fin n → Ω) (g : Fin q → Coordinate u)
    (f : Fin n → Fin s → Coordinate w) : Prop :=
  ∀ i, AcceptsWithCondition (A (ω i)) (f i) (condition ρ valid R (ω i) g)

noncomputable def projected {Ω : Type} {u w : ℕ}
    (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (D : Ω → Finset (Word w)) (ω : Ω) : Finset (Word u) :=
  ((D ω).filter (fun y ↦ valid ω y = true)).image (ρ ω)

axiom acceptance_bound {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (u w n s q : ℕ) (ρ : Ω → Word w → Word u) (valid : Ω → Coordinate w)
    (R : Table u) (A : Ω → Table w) (D : Ω → Finset (Word w))
    (B k : ℕ) (p δ : ℝ) (hp : 0 ≤ p)
    (hB : ∀ ω, (D ω).card ≤ B)
    (hdecode : ∀ ω h, probability (BadWithCondition (s := s) (A ω) (D ω) h) ≤ δ)
    (hpoint : ∀ x, probability (fun ω ↦ x ∈ projected ρ valid D ω) ≤ p)
    (hsmall : (n : ℝ) * B * p ≤ 1) :
    probability (fun z : ((Fin n → Ω) × (Fin q → Coordinate u)) ×
        (Fin n → Fin s → Coordinate w) ↦ Accepts ρ valid R A z.1.1 z.1.2 z.2) ≤
      n * δ + (2 : ℝ) ^ n * ((n : ℝ) * B * p) ^ (n - k) +
        (B : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (k + 1)) ^ q

end Lax253009.FAFTest
end
