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

/-- A complete Boolean proof with `m` positions. -/
abbrev Oracle (m : ℕ) := Fin m → Bool

/-- A partial proof; `none` means that the position is not queried. -/
abbrev View (m : ℕ) := Fin m → Option Bool

/-- The complete proof agrees with every specified answer in the local view. -/
def Extends {m : ℕ} (π : Oracle m) (a : View m) : Prop :=
  ∀ i b, a i = some b → π i = b

end Lax323828.LocalTests
end
