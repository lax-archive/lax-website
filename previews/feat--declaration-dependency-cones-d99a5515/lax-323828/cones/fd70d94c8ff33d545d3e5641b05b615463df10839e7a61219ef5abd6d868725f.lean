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

end Lax323828.LongCode
end

-- Lax323828.LongCodePatterns
section
namespace Lax323828.LongCodePatterns

open scoped Classical

open LongCode

/-- A partial Boolean answer table; `none` marks an unqueried coordinate. -/
abbrev Pattern (w : ℕ) := Coordinate w → Option Bool

end Lax323828.LongCodePatterns
end
