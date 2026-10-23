-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card

-- Lax496464.WH_B1_Structures
section
namespace Lax496464
end Lax496464

namespace Lax496464.WH_B1_Structures
end Lax496464.WH_B1_Structures

namespace Lax496464.WH_B1_Structures.Structure
end Lax496464.WH_B1_Structures.Structure
end

-- Lax496464.WH_B2_FirstOrder
section
namespace Lax496464.WH_B2_FirstOrder.Alt
end Lax496464.WH_B2_FirstOrder.Alt

namespace Lax496464.WH_B2_FirstOrder.Assignment
end Lax496464.WH_B2_FirstOrder.Assignment

namespace Lax496464.WH_B2_FirstOrder.Sat
end Lax496464.WH_B2_FirstOrder.Sat

namespace Lax496464.WH_B2_FirstOrder.Formula.ArityAtMost
end Lax496464.WH_B2_FirstOrder.Formula.ArityAtMost

namespace Lax496464.WH_B2_FirstOrder.Formula.IsPositive
end Lax496464.WH_B2_FirstOrder.Formula.IsPositive

namespace Lax496464.WH_B2_FirstOrder.Formula.IsQF
end Lax496464.WH_B2_FirstOrder.Formula.IsQF

namespace Lax496464.WH_B2_FirstOrder.Formula.NoSetVar
end Lax496464.WH_B2_FirstOrder.Formula.NoSetVar

namespace Lax496464.WH_B2_FirstOrder

open Lax496464.WH_B1_Structures

/-- First-order formulas, with atoms for the vocabulary's relation symbols and for one free relation
variable. -/
inductive Formula
  /-- The atom `R_i x_{a_1} … x_{a_r}`. -/
  | rel (i : ℕ) (xs : List ℕ)
  /-- The atom `X x_{a_1} … x_{a_s}` of the free relation variable. -/
  | setVar (xs : List ℕ)
  /-- The equation `x = y`. -/
  | eq (x y : ℕ)
  /-- Negation. -/
  | neg (φ : Formula)
  /-- Conjunction. -/
  | and (φ ψ : Formula)
  /-- Disjunction. -/
  | or (φ ψ : Formula)
  /-- Existential quantification. -/
  | ex (x : ℕ) (φ : Formula)
  /-- Universal quantification. -/
  | all (x : ℕ) (φ : Formula)

/-- The free (individual) variables of a formula. -/
def Formula.freeVars : Formula → Finset ℕ
  | .rel _ xs => xs.toFinset
  | .setVar xs => xs.toFinset
  | .eq x y => {x, y}
  | .neg φ => φ.freeVars
  | .and φ ψ => φ.freeVars ∪ ψ.freeVars
  | .or φ ψ => φ.freeVars ∪ ψ.freeVars
  | .ex x φ => φ.freeVars.erase x
  | .all x φ => φ.freeVars.erase x

/-- The formula is a **sentence**: it has no free individual variables (the relation variable may
occur). -/
def IsSentence (φ : Formula) : Prop := φ.freeVars = ∅

end Lax496464.WH_B2_FirstOrder
end
