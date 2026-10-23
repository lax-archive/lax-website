-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

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

end Lax783278.PositiveCNF
end
