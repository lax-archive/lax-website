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

end Lax323828.LocalTests
end
