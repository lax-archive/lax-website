-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

-- Lax323828.LocalTests
section
namespace Lax323828.LocalTests

open scoped Classical

/-- A complete Boolean proof with `m` positions. -/
abbrev Oracle (m : ℕ) := Fin m → Bool

/-- A partial proof; `none` means that the position is not queried. -/
abbrev View (m : ℕ) := Fin m → Option Bool

/-- The complete proof agrees with every specified answer in the local view. -/
def Extends {m : ℕ} (π : Oracle m) (a : View m) : Prop :=
  ∀ i b, a i = some b → π i = b

/-- For each random choice, the collection of local views that make the verifier accept. -/
structure System (r m : ℕ) where
  /-- The acceptable partial answer patterns for this random choice. -/
  accepting : Fin r → Finset (View m)

/-- The random choices on which the supplied proof extends an accepting view. -/
noncomputable def System.acceptedSeeds {r m : ℕ} (C : System r m)
    (π : Oracle m) : Finset (Fin r) :=
  Finset.univ.filter fun seed ↦ ∃ a ∈ C.accepting seed, Extends π a

end Lax323828.LocalTests
end
