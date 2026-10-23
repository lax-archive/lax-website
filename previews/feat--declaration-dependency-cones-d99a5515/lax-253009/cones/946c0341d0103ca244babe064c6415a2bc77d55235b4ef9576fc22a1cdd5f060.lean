-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Option
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

-- Lax253009.LongCodePatterns
section
namespace Lax253009.LongCodePatterns

open LongCode

abbrev Pattern (w : ℕ) := Coordinate w → Option Bool

noncomputable def restrict {w : ℕ} (Q : Coordinate w → Prop) (A : Table w) :
    Pattern w := by
  classical
  exact fun g ↦ if Q g then some (A g) else none

noncomputable def patterns {w s : ℕ} (f : Fin s → Coordinate w) : Finset (Pattern w) := by
  classical
  exact (Finset.univ.filter (fun A : Table w ↦ Accepts A f)).image (restrict (Queried f))

axiom free_bits {w s : ℕ} (f : Fin s → Coordinate w) :
  (patterns f).card ≤ 2 ^ s

end Lax253009.LongCodePatterns
end
