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
namespace Lax323828
end Lax323828

namespace Lax323828.FiniteProbability
end Lax323828.FiniteProbability
end

-- Lax323828.DecodedStrategies
section
namespace Lax323828.DecodedStrategies
end Lax323828.DecodedStrategies
end

-- Lax323828.LongCode
section
namespace Lax323828.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

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
end Lax323828.FAFTest
end

-- Lax323828.FAFStrategyExtraction
section
namespace Lax323828.FAFStrategyExtraction
end Lax323828.FAFStrategyExtraction
end

-- Lax323828.ProjectionEncoding
section
namespace Lax323828.ProjectionEncoding

open scoped Classical

open LongCode FiniteProbability

/-- Recover the unique encoded letter if `b` lies in the image of `e`; otherwise return no letter. -/
noncomputable def decode {A B : Type} (e : A ↪ B) (b : B) : Option A :=
  if h : ∃ a, e a = b then some h.choose else none

/-- Accept precisely the encodings of letters that satisfy the original validity test. -/
noncomputable def valid {U Ω Y : Type} {w : ℕ}
    (ey : Y ↪ Word w) (v : U → Ω → Y → Bool) (u : U) (ω : Ω) (b : Word w) : Bool :=
  match decode ey b with
  | some y => v u ω y
  | none => false

/-- Decode the first answer, apply the projection, and encode the second answer; invalid words map to the zero word. -/
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

end Lax323828.ProjectionEncoding
end
