-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

end Lax434930.PolynomialTime
end

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

-- Lax783278.PositiveCNF
section
namespace Lax783278
end Lax783278

namespace Lax783278.PositiveCNF
end Lax783278.PositiveCNF

namespace Lax783278.PositiveCNF.Formula
end Lax783278.PositiveCNF.Formula

namespace Lax783278.PositiveCNF.TrueWinsAfter
end Lax783278.PositiveCNF.TrueWinsAfter
end

-- Lax783278.Encoding
section
namespace Lax783278.Encoding

open scoped Classical

open Lax434930.PolynomialTime

structure Graph where
  vertices : ℕ
  graph : SimpleGraph (Fin vertices)

noncomputable def graphWord (G : Graph) : Word :=
  List.replicate G.vertices true ++ [false] ++
    (List.finRange G.vertices).flatMap fun u =>
      (List.finRange G.vertices).map fun v => decide (G.graph.Adj u v)

def arcKayles : Language :=
  {w | ∃ G : Graph, graphWord G = w ∧ ArcKayles.Winning G.graph Finset.univ}

end Lax783278.Encoding
end
