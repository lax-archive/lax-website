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

def evaluation {w : ℕ} (x : Word w) : Table w := fun g ↦ g x

def compose {w s : ℕ} (f : Fin s → Coordinate w) (B : Word s → Bool) : Coordinate w :=
  fun x ↦ B (fun i ↦ f i x)

def Accepts {w s : ℕ} (A : Table w) (f : Fin s → Coordinate w) : Prop :=
  ∀ B : Word s → Bool, A (compose f B) = B (fun i ↦ A (f i))

end Lax323828.LongCode
end

-- Lax323828.LongCodeCorrectness
section
namespace Lax323828.LongCodeCorrectness

open LongCode

axiom perfect_completeness {w s : ℕ} (x : Word w) (f : Fin s → Coordinate w) :
  Accepts (evaluation x) f

end Lax323828.LongCodeCorrectness
end
