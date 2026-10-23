-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Bitwise
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

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

/-- A winning strategy for the next player. There are at most `S.card` moves,
since every move removes vertices, so this many rounds evaluates the whole game. -/
def Winning (G : SimpleGraph V) (S : Finset V) : Prop :=
  WinningAfter G S.card S

end Lax783278.ArcKayles
end

-- Lax783278.Grundy
section
namespace Lax783278.Grundy

open ArcKayles

/-- The least natural number not in the finite set `S`. -/
noncomputable def mex (S : Finset ℕ) : ℕ := sInf {n : ℕ | n ∉ S}

/-- The game value obtained from `rounds` rounds of backward induction.
A position at depth zero has value zero; each further round takes the
minimum excluded value of its immediate successors. -/
noncomputable def valueAfter {V : Type} [DecidableEq V]
    (G : SimpleGraph V) : ℕ → Finset V → ℕ
  | 0, _ => 0
  | rounds + 1, S =>
      mex ((moves G S).image fun e => valueAfter G rounds (remove S e.1 e.2))

/-- The Sprague–Grundy value of the complete game tree. Its depth is at most
the number of surviving vertices, because every move removes two vertices. -/
noncomputable def value {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  valueAfter G S.card S

end Lax783278.Grundy
end

-- Lax783278.GrundyProperties
section
namespace Lax783278.GrundyProperties

open ArcKayles Grundy

axiom losing_iff_zero {V : Type} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    ¬ Winning G S ↔ value G S = 0

end Lax783278.GrundyProperties
end
