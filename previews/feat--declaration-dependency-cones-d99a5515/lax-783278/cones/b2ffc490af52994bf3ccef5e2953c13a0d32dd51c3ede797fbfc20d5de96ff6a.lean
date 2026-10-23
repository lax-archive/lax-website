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
namespace Lax783278
end Lax783278

namespace Lax783278.ArcKayles
end Lax783278.ArcKayles

namespace Lax783278.ArcKayles.WinningAfter
end Lax783278.ArcKayles.WinningAfter
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
namespace Lax783278.Encoding.Graph
end Lax783278.Encoding.Graph

namespace Lax783278.Encoding

open scoped Classical

open Lax434930.PolynomialTime

def formulaWord (φ : PositiveCNF.Formula) : Word :=
  List.replicate φ.nvars true ++ [false] ++
    List.replicate φ.clauses.length true ++ [false] ++
    φ.clauses.flatMap fun C =>
      (List.finRange φ.nvars).map fun x => decide (x ∈ C)

def positiveCNF : Language :=
  {w | ∃ φ : PositiveCNF.Formula, formulaWord φ = w ∧ PositiveCNF.FirstWins φ}

end Lax783278.Encoding
end
