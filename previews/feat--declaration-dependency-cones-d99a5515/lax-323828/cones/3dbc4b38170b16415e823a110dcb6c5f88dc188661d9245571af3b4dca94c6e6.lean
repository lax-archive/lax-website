-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

-- Lax323828.FiniteProbability
section
namespace Lax323828.FiniteProbability

open scoped Classical

open scoped BigOperators

/-- The proportion of points in the finite sample space satisfying the event `P`. -/
noncomputable def probability {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end Lax323828.FiniteProbability
end

-- Lax323828.DecodedStrategies
section
namespace Lax323828.DecodedStrategies

open FiniteProbability

def Wins {U Ω W X Y : Type}
    (question : U → Ω → W) (V : U → Ω → Y → X → Prop)
    (P : W → Option Y) (Q : U → Option X) (z : U × Ω) : Prop :=
  ∃ y x, P (question z.1 z.2) = some y ∧ Q z.1 = some x ∧ V z.1 z.2 y x

end Lax323828.DecodedStrategies
end

-- Lax323828.LongCode
section
namespace Lax323828.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

abbrev Table (w : ℕ) := Coordinate w → Bool

def compose {w s : ℕ} (f : Fin s → Coordinate w) (B : Word s → Bool) : Coordinate w :=
  fun x ↦ B (fun i ↦ f i x)

def Accepts {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w) : Prop :=
  ∀ B : Word s → Bool, A (compose f B) = B (fun i ↦ A (f i))

def AgreesOn {w : ℕ} (h g g' : Coordinate w) : Prop :=
  ∀ x, h x = true → g x = g' x

def Queried {w s : ℕ} (f : Fin s → Coordinate w) (g : Coordinate w) : Prop :=
  (∃ i, g = f i) ∨ ∃ B : Word s → Bool, g = compose f B

def AcceptsWithCondition {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w)
    (h : Coordinate w) : Prop :=
  Accepts A f ∧ ∀ g, Queried f g → ∀ g', AgreesOn h g g' → A g = A g'

end Lax323828.LongCode
end

-- Lax323828.CNASoundness
section
namespace Lax323828.CNASoundness
end Lax323828.CNASoundness
end

-- Lax323828.ManyTableConsistency
section
namespace Lax323828.ManyTableConsistency
end Lax323828.ManyTableConsistency
end

-- Lax323828.FAFTest
section
namespace Lax323828.FAFTest

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

end Lax323828.FAFTest
end

-- Lax323828.FAFStrategyExtraction
section
namespace Lax323828.FAFStrategyExtraction

open LongCode FiniteProbability

abbrev Seed (Ω : Type) (u w n s q : ℕ) :=
  ((Fin n → Ω) × (Fin q → Coordinate u)) × (Fin n → Fin s → Coordinate w)

def Relation {U Ω : Type} {u w : ℕ}
    (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
    (v : U) (ω : Ω) (y : Word w) (x : Word u) : Prop :=
  valid v ω y = true ∧ ρ v ω y = x

def Accepts {U Ω W : Type} {u w n s q : ℕ} (question : U → Ω → W)
    (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
    (R : U → Table u) (A : W → Table w) (z : U × Seed Ω u w n s q) : Prop :=
  FAFTest.Accepts (ρ z.1) (valid z.1) (R z.1) (fun ω ↦ A (question z.1 ω))
    z.2.1.1 z.2.1.2 z.2.2

noncomputable def errorBound (n B k q : ℕ) (p δ : ℝ) : ℝ :=
  n * δ + (2 : ℝ) ^ n * ((n : ℝ) * B * p) ^ (n - k) +
    (B : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (k + 1)) ^ q

/-- Apply the proved asymptotic CNA theorem uniformly to the entire family
of first-prover tables. No decoding or soundness hypothesis is required. -/
axiom uniform_extraction (K : ℕ) (hK : 0 < K) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
      ∀ {U Ω W : Type} [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
        [Fintype W] [DecidableEq W],
      ∀ u n q k : ℕ, ∀ (question : U → Ω → W)
        (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
        (R : U → Table u) (A : W → Table w) (p : ℝ),
        0 ≤ p → (n : ℝ) * (2 : ℝ) ^ s * p ≤ 1 →
        ∃ P : W → Option (Word w), ∃ Q : U → Option (Word u),
          (probability (Accepts (n := n) (s := s) (q := q) question ρ valid R A) -
            errorBound n (2 ^ s) k q p (Real.rpow 2 (-(K : ℝ) * (s : ℝ)))) * p / ((2 : ℝ) ^ s + 1) ≤
          probability (DecodedStrategies.Wins question (Relation ρ valid) P Q)

end Lax323828.FAFStrategyExtraction
end
