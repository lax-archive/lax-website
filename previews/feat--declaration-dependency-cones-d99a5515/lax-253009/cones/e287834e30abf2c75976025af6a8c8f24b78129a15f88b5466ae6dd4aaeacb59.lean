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
namespace Lax253009
end Lax253009

namespace Lax253009.FiniteProbability
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

end Lax253009.LongCode
end

-- Lax253009.CNASoundness
section
namespace Lax253009.CNASoundness

open LongCode FiniteProbability

def Bad {w s : ℕ} (A : Table w) (S : Finset (Word w))
    (f : Fin s → Coordinate w) : Prop :=
  Accepts A f ∧ ¬ ∃ x ∈ S, LooksLike A f x

end Lax253009.CNASoundness
end
