-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

-- Lax253009.LocalTests
section
namespace Lax253009.LocalTests.System
end Lax253009.LocalTests.System

namespace Lax253009.LocalTests

abbrev Oracle (m : ℕ) := Fin m → Bool

abbrev View (m : ℕ) := Fin m → Option Bool

def Extends {m : ℕ} (π : Oracle m) (a : View m) : Prop :=
  ∀ i b, a i = some b → π i = b

end Lax253009.LocalTests
end
