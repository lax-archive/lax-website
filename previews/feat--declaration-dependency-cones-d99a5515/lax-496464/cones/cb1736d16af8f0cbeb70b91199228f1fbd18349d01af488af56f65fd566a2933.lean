-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card

-- Lax496464.WH_B1_Structures
section
namespace Lax496464.WH_B1_Structures.Structure
end Lax496464.WH_B1_Structures.Structure

namespace Lax496464.WH_B1_Structures

open scoped BigOperators

/-- The block of one relation: the number of its tuples, then the tuples, in some order without
repetition. -/
def EncodesRel (R : Finset (List ℕ)) (blk : List ℕ) : Prop :=
  ∃ ts : List (List ℕ), ts.Nodup ∧ ts.toFinset = R ∧ blk = ts.length :: ts.flatten

end Lax496464.WH_B1_Structures
end
