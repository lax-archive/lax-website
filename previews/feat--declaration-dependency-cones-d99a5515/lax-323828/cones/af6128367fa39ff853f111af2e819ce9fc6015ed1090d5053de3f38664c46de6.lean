-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Pi

-- Lax323828.LongCode
section
namespace Lax323828.LongCode

abbrev Word (w : ℕ) := Fin w → Bool

abbrev Coordinate (w : ℕ) := Word w → Bool

end Lax323828.LongCode
end

-- Lax323828.OddNormalization
section
namespace Lax323828.OddNormalization

open LongCode

def negate {w : ℕ} (g : Coordinate w) : Coordinate w := fun x ↦ !(g x)

end Lax323828.OddNormalization
end
