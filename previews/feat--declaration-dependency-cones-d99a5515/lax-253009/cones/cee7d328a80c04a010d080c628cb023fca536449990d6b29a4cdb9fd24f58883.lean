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
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
end Lax253009.FiniteProbability
end

-- Lax253009.DecodedStrategies
section
namespace Lax253009.DecodedStrategies
end Lax253009.DecodedStrategies
end

-- Lax253009.LongCode
section
namespace Lax253009.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

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

axiom completeness {U Ω W X Y : Type} {u w : ℕ}
    (ex : X ↪ Word u) (ey : Y ↪ Word w) (question : U → Ω → W)
    (v : U → Ω → Y → Bool) (ρ : U → Ω → Y → X)
    (P : W → Y) (Q : U → X)
    (hv : ∀ a ω, v a ω (P (question a ω)) = true)
    (hρ : ∀ a ω, ρ a ω (P (question a ω)) = Q a) :
    (∀ a ω, valid ey v a ω (ey (P (question a ω))) = true) ∧
    (∀ a ω, project ex ey ρ a ω (ey (P (question a ω))) = ex (Q a))

end Lax253009.ProjectionEncoding
end
