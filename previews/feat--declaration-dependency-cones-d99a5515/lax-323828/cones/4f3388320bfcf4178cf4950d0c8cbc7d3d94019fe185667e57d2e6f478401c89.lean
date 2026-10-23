-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Option
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

def Queried {w s : ℕ} (f : Fin s → Coordinate w) (g : Coordinate w) : Prop :=
  (∃ i, g = f i) ∨ ∃ B : Word s → Bool, g = compose f B

end Lax323828.LongCode
end

-- Lax323828.LongCodePatterns
section
namespace Lax323828.LongCodePatterns

open scoped Classical

open LongCode

/-- A partial Boolean answer table; `none` marks an unqueried coordinate. -/
abbrev Pattern (w : ℕ) := Coordinate w → Option Bool

/-- Record the table answers on the queried coordinates and leave the others unspecified. -/
noncomputable def restrict {w : ℕ} (Q : Coordinate w → Prop) (A : Table w) :
    Pattern w :=
  fun g ↦ if Q g then some (A g) else none

/-- All queried answer patterns arising from accepting tables. -/
noncomputable def patterns {w s : ℕ} (f : Fin s → Coordinate w) : Finset (Pattern w) :=
  (Finset.univ.filter (fun A : Table w ↦ Accepts A f)).image (restrict (Queried f))

axiom free_bits {w s : ℕ} (f : Fin s → Coordinate w) :
  (patterns f).card ≤ 2 ^ s

end Lax323828.LongCodePatterns
end
