-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Pi

-- Lax253009.LongCode
section
namespace Lax253009.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

abbrev Table (w : ℕ) := Coordinate w → Bool

end Lax253009.LongCode
end

-- Lax253009.OddNormalization
section
namespace Lax253009.OddNormalization

open LongCode

def negate {w : ℕ} (g : Coordinate w) : Coordinate w := fun x ↦ !(g x)

def oddify {w : ℕ} (x₀ : Word w) (A : Table w) : Table w :=
  fun g ↦ if A (negate g) = !(A g) then A g else g x₀

axiom odd {w : ℕ} (x₀ : Word w) (A : Table w) (g : Coordinate w) :
  oddify x₀ A (negate g) = !(oddify x₀ A g)

end Lax253009.OddNormalization
end
