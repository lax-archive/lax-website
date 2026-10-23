-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Log

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
namespace Lax783278.PositiveCNF

/-- A conjunction of clauses, each a disjunction of positive variables. -/
structure Formula where
  /-- Number of variables, labeled from zero. -/
  nvars : ℕ
  /-- The clauses; an empty clause makes the formula unsatisfiable. -/
  clauses : List (Finset (Fin nvars))

/-- Every clause contains a variable belonging to the true set `T`. -/
def Satisfied (φ : Formula) (T : Finset (Fin φ.nvars)) : Prop :=
  ∀ C ∈ φ.clauses, ∃ x ∈ C, x ∈ T

/-- Evaluate the game for a specified number of remaining rounds.
At a True turn some choice must win; at a False turn every choice must win.
A completed assignment is evaluated by the formula's satisfaction rule. -/
def TrueWinsAfter (φ : Formula) : ℕ → Finset (Fin φ.nvars) →
    Finset (Fin φ.nvars) → Bool → Prop
  | 0, _, T, _ => Satisfied φ T
  | rounds + 1, U, T, trueTurn =>
      if U = ∅ then Satisfied φ T
      else if trueTurn then
        ∃ x ∈ U, TrueWinsAfter φ rounds (U.erase x) (insert x T) false
      else
        ∀ x ∈ U, TrueWinsAfter φ rounds (U.erase x) T true

/-- Whether True can force satisfaction. Exactly `U.card` assignments remain,
so that many rounds suffice to evaluate every possible continuation. -/
def TrueWins (φ : Formula) (U T : Finset (Fin φ.nvars)) (trueTurn : Bool) : Prop :=
  TrueWinsAfter φ U.card U T trueTurn

/-- True wins the initial game, with every variable unassigned and True to move. -/
def FirstWins (φ : Formula) : Prop := TrueWins φ Finset.univ ∅ true

end Lax783278.PositiveCNF
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

def formulaWord (φ : PositiveCNF.Formula) : Word :=
  List.replicate φ.nvars true ++ [false] ++
    List.replicate φ.clauses.length true ++ [false] ++
    φ.clauses.flatMap fun C =>
      (List.finRange φ.nvars).map fun x => decide (x ∈ C)

def arcKayles : Language :=
  {w | ∃ G : Graph, graphWord G = w ∧ ArcKayles.Winning G.graph Finset.univ}

def positiveCNF : Language :=
  {w | ∃ φ : PositiveCNF.Formula, formulaWord φ = w ∧ PositiveCNF.FirstWins φ}

end Lax783278.Encoding
end

-- Lax783278.Construction
section
namespace Lax783278.Construction
end Lax783278.Construction
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075.Reductions

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

def ManyOne (A B : Language) : Prop :=
  ∃ f : Word → Word, Nonempty (Turing.TM2ComputableInPolyTime id id f) ∧
    ∀ x, x ∈ A ↔ f x ∈ B

end Lax429075.Reductions
end

-- Lax434930.SpaceMachines
section
namespace Lax434930.SpaceMachines.Configuration
end Lax434930.SpaceMachines.Configuration

namespace Lax434930.SpaceMachines.readInput
end Lax434930.SpaceMachines.readInput

namespace Lax434930.SpaceMachines.Machine.Run
end Lax434930.SpaceMachines.Machine.Run

namespace Lax434930.SpaceMachines.Move.apply
end Lax434930.SpaceMachines.Move.apply

set_option backward.isDefEq.respectTransparency false

namespace Lax434930.SpaceMachines

open PolynomialTime

/-- The input alphabet, with two distinct endmarkers. -/
inductive InputSymbol
  | leftEnd
  | bit (value : Bool)
  | rightEnd
  deriving DecidableEq, Fintype

/-- An elementary head movement, including staying in place. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq, Fintype

/-- One local transition: change state, write a work symbol, and move the heads. -/
structure Action (Γ Q : Type) where
  state : Q
  write : Γ
  inputMove : Move
  workMove : Move

/-- The complete finite description of a possibly nondeterministic machine. -/
structure Machine where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [control : Fintype Q]
  blank : Γ
  start : Q
  transition : Q → InputSymbol → Γ → Finset (Action Γ Q)
  accept : Q → Bool

attribute [instance] Machine.alphabet Machine.control

end Lax434930.SpaceMachines
end

-- Lax434930.SpaceBounds
section
namespace Lax434930.SpaceBounds
end Lax434930.SpaceBounds
end

-- Lax434930.PolynomialSpace
section
namespace Lax434930.PolynomialSpace
end Lax434930.PolynomialSpace
end

-- Lax783278.PSPACE
section
namespace Lax783278
end Lax783278

namespace Lax783278.PSPACE
end Lax783278.PSPACE
end

-- Lax783278.Reduction
section
namespace Lax783278.Reduction

open PositiveCNF Construction ArcKayles

axiom polynomial_reduction :
    Lax429075.Reductions.ManyOne Encoding.positiveCNF Encoding.arcKayles

end Lax783278.Reduction
end
