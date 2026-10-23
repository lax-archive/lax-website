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
namespace Lax496464.WH_B2_FirstOrder.Assignment
end Lax496464.WH_B2_FirstOrder.Assignment

namespace Lax496464.WH_B2_FirstOrder.Sat
end Lax496464.WH_B2_FirstOrder.Sat

namespace Lax496464.WH_B2_FirstOrder.Formula.ArityAtMost
end Lax496464.WH_B2_FirstOrder.Formula.ArityAtMost

namespace Lax496464.WH_B2_FirstOrder.Formula.IsPositive
end Lax496464.WH_B2_FirstOrder.Formula.IsPositive

namespace Lax496464.WH_B2_FirstOrder.Formula.NoSetVar
end Lax496464.WH_B2_FirstOrder.Formula.NoSetVar

namespace Lax496464.WH_B2_FirstOrder.Formula.freeVars
end Lax496464.WH_B2_FirstOrder.Formula.freeVars

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

/-- The formula is quantifier-free. -/
def Formula.IsQF : Formula → Prop
  | .ex _ _ => False
  | .all _ _ => False
  | .neg φ => φ.IsQF
  | .and φ ψ => φ.IsQF ∧ ψ.IsQF
  | .or φ ψ => φ.IsQF ∧ ψ.IsQF
  | _ => True

/-- A block of existential quantifiers over the variables `xs`. -/
def Formula.exBlock (xs : List ℕ) (φ : Formula) : Formula := xs.foldr Formula.ex φ

/-- A block of universal quantifiers over the variables `xs`. -/
def Formula.allBlock (xs : List ℕ) (φ : Formula) : Formula := xs.foldr Formula.all φ

/-- `Alt true t φ` is `φ ∈ Σ_t` and `Alt false t φ` is `φ ∈ Π_t`: `t` alternating blocks of
quantifiers, the first existential or universal respectively, in front of a quantifier-free
formula. -/
def Alt : Bool → ℕ → Formula → Prop
  | _, 0, φ => φ.IsQF
  | true, t + 1, φ => ∃ xs ψ, φ = Formula.exBlock xs ψ ∧ Alt false t ψ
  | false, t + 1, φ => ∃ xs ψ, φ = Formula.allBlock xs ψ ∧ Alt true t ψ

end Lax496464.WH_B2_FirstOrder
end
