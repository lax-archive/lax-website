-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card

-- Lax496464.WH_B1_Structures
section
namespace Lax496464.WH_B1_Structures

open scoped BigOperators

/-- A finite relational structure. -/
structure Structure where
  /-- The vocabulary: the arities of the relation symbols `0, 1, …`. -/
  arities : List ℕ
  /-- The universe is `{0, …, size - 1}`. -/
  size : ℕ
  /-- The relation of each symbol, as a set of tuples. -/
  rel : ℕ → Finset (List ℕ)
  /-- Every arity is at least one. -/
  arity_pos : ∀ a ∈ arities, 1 ≤ a
  /-- The tuples of symbol `i` have its arity and entries in the universe; other symbols have no
  tuples. -/
  wf : ∀ i, ∀ t ∈ rel i, i < arities.length ∧ t.length = arities.getD i 0 ∧ ∀ a ∈ t, a < size

end Lax496464.WH_B1_Structures
end

-- Lax496464.WH_B2_FirstOrder
section
namespace Lax496464.WH_B2_FirstOrder.Alt
end Lax496464.WH_B2_FirstOrder.Alt

namespace Lax496464.WH_B2_FirstOrder.Formula.ArityAtMost
end Lax496464.WH_B2_FirstOrder.Formula.ArityAtMost

namespace Lax496464.WH_B2_FirstOrder.Formula.IsPositive
end Lax496464.WH_B2_FirstOrder.Formula.IsPositive

namespace Lax496464.WH_B2_FirstOrder.Formula.IsQF
end Lax496464.WH_B2_FirstOrder.Formula.IsQF

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

/-- An assignment of universe elements to variables. -/
abbrev Assignment := ℕ → ℕ

/-- The assignment `ρ` changed to send `x` to `a`. -/
def Assignment.update (ρ : Assignment) (x a : ℕ) : Assignment :=
  fun y => if y = x then a else ρ y

/-- **Satisfaction.** The formula holds in `A`, with the relation variable interpreted as `S`,
under the assignment `ρ`. -/
def Sat (A : Structure) (S : Set (List ℕ)) : Formula → Assignment → Prop
  | .rel i xs, ρ => xs.map ρ ∈ A.rel i
  | .setVar xs, ρ => xs.map ρ ∈ S
  | .eq x y, ρ => ρ x = ρ y
  | .neg φ, ρ => ¬ Sat A S φ ρ
  | .and φ ψ, ρ => Sat A S φ ρ ∧ Sat A S ψ ρ
  | .or φ ψ, ρ => Sat A S φ ρ ∨ Sat A S ψ ρ
  | .ex x φ, ρ => ∃ a, a < A.size ∧ Sat A S φ (ρ.update x a)
  | .all x φ, ρ => ∀ a, a < A.size → Sat A S φ (ρ.update x a)

end Lax496464.WH_B2_FirstOrder
end
