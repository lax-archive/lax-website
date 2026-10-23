-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
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

-- Lax253009.DecodedStrategies
section
namespace Lax253009.DecodedStrategies

open FiniteProbability

def Common {U Ω W X Y : Type} [Fintype Ω]
    (question : U → Ω → W) (V : U → Ω → Y → X → Prop)
    (D : W → Finset Y) (p : ℝ) (u : U) : Prop :=
  ∃ x, p ≤ probability (fun ω ↦ ∃ y ∈ D (question u ω), V u ω y x)

end Lax253009.DecodedStrategies
end
