-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.ModelTheory.Semantics

-- Lax945089.EhrenfeuchtGames
section
namespace Lax945089.EhrenfeuchtGames.efStage
end Lax945089.EhrenfeuchtGames.efStage

namespace Lax945089.EhrenfeuchtGames.qdepth
end Lax945089.EhrenfeuchtGames.qdepth

namespace Lax945089.EhrenfeuchtGames

open FirstOrder

open Language Structure

/-- A **legal position** of the Ehrenfeucht–Fraïssé game: two tuples of equal
length, one on each side, satisfying the same equalities between their
coordinates and the same base relations at every selection of coordinates.
Equivalently, matching coordinate to coordinate is a partial isomorphism. -/
def PartialIso (L : Language.{0, 0}) {M N : Type} [L.Structure M] [L.Structure N] {j : ℕ}
    (a : Fin j → M) (b : Fin j → N) : Prop :=
  (∀ i i' : Fin j, a i = a i' ↔ b i = b i') ∧
    ∀ (l : ℕ) (R : L.Relations l) (g : Fin l → Fin j),
      ((RelMap R fun p => a (g p)) ↔ RelMap R fun p => b (g p))

end Lax945089.EhrenfeuchtGames
end
