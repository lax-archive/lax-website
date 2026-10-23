-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

-- Lax825442.TwinCover
section
namespace Lax825442.TwinCover

/-- Adjacent vertices with the same neighbors outside the pair. -/
def TrueTwins {V : Type} (G : SimpleGraph V) (u v : V) : Prop :=
  G.Adj u v ∧ (∀ w : V,
    (w ≠ u ∧ w ≠ v) → (G.Adj u w ↔ G.Adj v w))

/-- A set meeting every edge except those between true twins. -/
def IsTwinCover {V : Type} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ ⦃u v : V⦄,
    (G.Adj u v ∧ ¬ TrueTwins G u v) → (u ∈ S ∨ v ∈ S)

end Lax825442.TwinCover
end
