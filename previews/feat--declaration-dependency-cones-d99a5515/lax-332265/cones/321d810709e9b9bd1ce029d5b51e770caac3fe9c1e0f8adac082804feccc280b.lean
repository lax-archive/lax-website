-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic

-- Lax332265.SixColorable
section
namespace Lax332265.SixColorable

/-- A graph admits a proper vertex colouring with the six colours in `Fin 6`. -/
def IsSixColorable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ colour : V → Fin 6,
    ∀ ⦃u v : V⦄, G.Adj u v → colour u ≠ colour v

end Lax332265.SixColorable
end
