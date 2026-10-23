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

def Wins {U Ω W X Y : Type}
    (question : U → Ω → W) (V : U → Ω → Y → X → Prop)
    (P : W → Option Y) (Q : U → Option X) (z : U × Ω) : Prop :=
  ∃ y x, P (question z.1 z.2) = some y ∧ Q z.1 = some x ∧ V z.1 z.2 y x

end Lax253009.DecodedStrategies
end

-- Lax253009.LongCode
section
namespace Lax253009.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

end Lax253009.LongCode
end

-- Lax253009.CNASoundness
section
namespace Lax253009.CNASoundness
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
end Lax253009.FAFTest
end

-- Lax253009.FAFStrategyExtraction
section
namespace Lax253009.FAFStrategyExtraction

open LongCode FiniteProbability

def Relation {U Ω : Type} {u w : ℕ}
    (ρ : U → Ω → Word w → Word u) (valid : U → Ω → Coordinate w)
    (v : U) (ω : Ω) (y : Word w) (x : Word u) : Prop :=
  valid v ω y = true ∧ ρ v ω y = x

end Lax253009.FAFStrategyExtraction
end

-- Lax253009.ProjectionEncoding
section
namespace Lax253009.ProjectionEncoding

open LongCode FiniteProbability

noncomputable def decode {A B : Type} (e : A ↪ B) (b : B) : Option A := by
  classical
  exact if h : ∃ a, e a = b then some h.choose else none

noncomputable def valid {U Ω Y : Type} {w : ℕ}
    (ey : Y ↪ Word w) (v : U → Ω → Y → Bool) (u : U) (ω : Ω) (b : Word w) : Bool :=
  match decode ey b with
  | some y => v u ω y
  | none => false

noncomputable def project {U Ω X Y : Type} {u w : ℕ}
    (ex : X ↪ Word u) (ey : Y ↪ Word w) (ρ : U → Ω → Y → X)
    (v : U) (ω : Ω) (b : Word w) : Word u :=
  match decode ey b with
  | some y => ex (ρ v ω y)
  | none => fun _ ↦ false

axiom soundness {U Ω W X Y : Type} [Fintype U] [Fintype Ω]
    [Nonempty X] [Nonempty Y] {u w : ℕ}
    (ex : X ↪ Word u) (ey : Y ↪ Word w) (question : U → Ω → W)
    (v : U → Ω → Y → Bool) (ρ : U → Ω → Y → X) (s : ℝ)
    (h : ∀ (P : W → Y) (Q : U → X),
      probability (fun z : U × Ω ↦ v z.1 z.2 (P (question z.1 z.2)) = true ∧
        ρ z.1 z.2 (P (question z.1 z.2)) = Q z.1) ≤ s)
    (P : W → Option (Word w)) (Q : U → Option (Word u)) :
    probability (DecodedStrategies.Wins question
      (FAFStrategyExtraction.Relation (project ex ey ρ) (valid ey v)) P Q) ≤ s

end Lax253009.ProjectionEncoding
end
