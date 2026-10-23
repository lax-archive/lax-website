-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
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

def Common {U Ω W X Y : Type} [Fintype Ω]
    (question : U → Ω → W) (V : U → Ω → Y → X → Prop)
    (D : W → Finset Y) (p : ℝ) (u : U) : Prop :=
  ∃ x, p ≤ probability (fun ω ↦ ∃ y ∈ D (question u ω), V u ω y x)

def Wins {U Ω W X Y : Type}
    (question : U → Ω → W) (V : U → Ω → Y → X → Prop)
    (P : W → Option Y) (Q : U → Option X) (z : U × Ω) : Prop :=
  ∃ y x, P (question z.1 z.2) = some y ∧ Q z.1 = some x ∧ V z.1 z.2 y x

axiom extract_strategies {U Ω W X Y : Type}
    [Fintype U] [Nonempty U] [Fintype Ω] [Nonempty Ω]
    [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y]
    (question : U → Ω → W) (V : U → Ω → Y → X → Prop)
    (D : W → Finset Y) (B : ℕ) (hB : ∀ w, (D w).card ≤ B)
    (p : ℝ) (hp : 0 ≤ p) :
    ∃ P : W → Option Y, ∃ Q : U → Option X,
      probability (Common question V D p) * p / (B + 1) ≤ probability (Wins question V P Q)

end Lax323828.DecodedStrategies
end
