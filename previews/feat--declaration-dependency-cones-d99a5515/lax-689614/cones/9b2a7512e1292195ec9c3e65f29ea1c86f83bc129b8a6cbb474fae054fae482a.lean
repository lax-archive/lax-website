-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

-- Lax689614.PositiveCNF
section
namespace Lax689614.PositiveCNF

structure Formula where
  nvars : ℕ
  clauses : List (Finset (Fin nvars))

def Satisfied (φ : Formula) (T : Finset (Fin φ.nvars)) : Prop :=
  ∀ C ∈ φ.clauses, ∃ x ∈ C, x ∈ T

/-- Whether True can force satisfaction from the specified position and turn. -/
def TrueWins (φ : Formula) (U T : Finset (Fin φ.nvars)) (trueTurn : Bool) : Prop :=
  if U = ∅ then Satisfied φ T
  else if trueTurn then
    ∃ x : U, TrueWins φ (U.erase x.val) (insert x.val T) false
  else
    ∀ x : U, TrueWins φ (U.erase x.val) T true
termination_by U.card
decreasing_by all_goals exact Finset.card_erase_lt_of_mem x.property

def FirstWins (φ : Formula) : Prop := TrueWins φ Finset.univ ∅ true

end Lax689614.PositiveCNF
end
