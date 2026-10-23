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

def compose {w s : ℕ} (f : Fin s → Coordinate w) (B : Word s → Bool) : Coordinate w :=
  fun x ↦ B (fun i ↦ f i x)

def Accepts {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w) : Prop :=
  ∀ B : Word s → Bool, A (compose f B) = B (fun i ↦ A (f i))

def Queried {w s : ℕ} (f : Fin s → Coordinate w) (g : Coordinate w) : Prop :=
  (∃ i, g = f i) ∨ ∃ B : Word s → Bool, g = compose f B

end Lax253009.LongCode
end

-- Lax253009.OddNormalization
section
namespace Lax253009.OddNormalization

open LongCode

def negate {w : ℕ} (g : Coordinate w) : Coordinate w := fun x ↦ !(g x)

def oddify {w : ℕ} (x₀ : Word w) (A : Table w) : Table w :=
  fun g ↦ if A (negate g) = !(A g) then A g else g x₀

axiom same_queries {w s : ℕ} (x₀ : Word w) (A : Table w)
    (f : Fin s → Coordinate w) (hA : Accepts A f)
    (g : Coordinate w) (hg : Queried f g) : oddify x₀ A g = A g

end Lax253009.OddNormalization
end
