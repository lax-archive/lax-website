-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

-- Lax783278.ArcKayles
section
namespace Lax783278.ArcKayles

open scoped Classical

variable {V : Type} [DecidableEq V]

/-- The position after playing an edge with endpoints `u` and `v`. -/
def remove (S : Finset V) (u v : V) : Finset V := (S.erase u).erase v

/-- Legal moves, represented by ordered pairs of endpoints. -/
noncomputable def moves (G : SimpleGraph V) (S : Finset V) : Finset (V × V) :=
  (S ×ˢ S).filter fun e => G.Adj e.1 e.2

/-- Backward induction through `rounds` moves. With no rounds left the
player to move loses; otherwise a winning move leaves a losing position. -/
def WinningAfter (G : SimpleGraph V) : ℕ → Finset V → Prop
  | 0, _ => False
  | rounds + 1, S =>
      ∃ e ∈ moves G S, ¬ WinningAfter G rounds (remove S e.1 e.2)

end Lax783278.ArcKayles
end
