-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

-- Lax323828.LocalTests
section
namespace Lax323828.LocalTests.System
end Lax323828.LocalTests.System

namespace Lax323828.LocalTests

open scoped Classical

/-- A partial proof; `none` means that the position is not queried. -/
abbrev View (m : ℕ) := Fin m → Option Bool

/-- The two partial views agree at all positions where both specify an answer. -/
def Compatible {m : ℕ} (a b : View m) : Prop :=
  ∀ i x y, a i = some x → b i = some y → x = y

end Lax323828.LocalTests
end
