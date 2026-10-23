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

end Lax323828.DecodedStrategies
end
