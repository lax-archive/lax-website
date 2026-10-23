-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

-- Lax689614.PositiveCNF
section
namespace Lax689614.PositiveCNF.TrueWins
end Lax689614.PositiveCNF.TrueWins

namespace Lax689614.PositiveCNF

structure Formula where
  nvars : ℕ
  clauses : List (Finset (Fin nvars))

def Satisfied (φ : Formula) (T : Finset (Fin φ.nvars)) : Prop :=
  ∀ C ∈ φ.clauses, ∃ x ∈ C, x ∈ T

end Lax689614.PositiveCNF
end

-- Lax689614.Passes
section
namespace Lax689614.Passes

open PositiveCNF

def TrueWins (φ : Formula) (U T : Finset (Fin φ.nvars))
    (trueTurn : Bool) (passes : ℕ) : Prop :=
  if U = ∅ then Satisfied φ T
  else if trueTurn then
    (∃ x : U, ∃ b : Bool,
      TrueWins φ (U.erase x.val) (if b then insert x.val T else T) false passes) ∨
    (∃ _h : 0 < passes, TrueWins φ U T false (passes - 1))
  else
    (∀ x : U, ∀ b : Bool,
      TrueWins φ (U.erase x.val) (if b then insert x.val T else T) true passes) ∧
    (∀ _h : 0 < passes, TrueWins φ U T true (passes - 1))
termination_by U.card + passes
decreasing_by
  all_goals first
    | have := Finset.card_erase_lt_of_mem x.property; omega
    | omega

end Lax689614.Passes
end
