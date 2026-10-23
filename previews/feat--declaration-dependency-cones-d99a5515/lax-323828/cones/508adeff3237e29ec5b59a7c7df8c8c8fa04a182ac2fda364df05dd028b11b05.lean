-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Pi

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

end Lax323828.LongCode
end

-- Lax323828.OddNormalization
section
namespace Lax323828.OddNormalization

open LongCode

def negate {w : ℕ} (g : Coordinate w) : Coordinate w := fun x ↦ !(g x)

def oddify {w : ℕ} (x₀ : Word w) (A : Table w) : Table w :=
  fun g ↦ if A (negate g) = !(A g) then A g else g x₀

axiom preserves_acceptance {w s : ℕ} (x₀ : Word w) (A : Table w)
    (f : Fin s → Coordinate w) (hA : Accepts A f) :
  Accepts (oddify x₀ A) f

end Lax323828.OddNormalization
end
