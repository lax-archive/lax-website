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

-- Lax783278.Passes
section
namespace Lax783278.Passes

open PositiveCNF

/-- Evaluate the game with passes for a fixed number of remaining rounds.
At a True turn one successful move suffices; at a False turn every legal
move must preserve True's win. Assignments and passes each use one round. -/
def TrueWinsAfter (φ : Formula) : ℕ → Finset (Fin φ.nvars) →
    Finset (Fin φ.nvars) → Bool → ℕ → Prop
  | 0, _, T, _, _ => Satisfied φ T
  | rounds + 1, U, T, trueTurn, passes =>
      if U = ∅ then Satisfied φ T
      else if trueTurn then
        (∃ x ∈ U, ∃ b : Bool,
          TrueWinsAfter φ rounds (U.erase x) (if b then insert x T else T) false passes) ∨
        (0 < passes ∧ TrueWinsAfter φ rounds U T false (passes - 1))
      else
        (∀ x ∈ U, ∀ b : Bool,
          TrueWinsAfter φ rounds (U.erase x) (if b then insert x T else T) true passes) ∧
        (0 < passes → TrueWinsAfter φ rounds U T true (passes - 1))

/-- True has a winning strategy with the given supply of passes.
There are at most `U.card + passes` moves before all variables are assigned. -/
def TrueWins (φ : Formula) (U T : Finset (Fin φ.nvars))
    (trueTurn : Bool) (passes : ℕ) : Prop :=
  TrueWinsAfter φ (U.card + passes) U T trueTurn passes

axiom outcome_equivalent (φ : Formula) (U T : Finset (Fin φ.nvars))
    (hd : Disjoint U T) (turn : Bool) (passes : ℕ) :
    TrueWins φ U T turn passes ↔ PositiveCNF.TrueWins φ U T turn

end Lax783278.Passes
end
