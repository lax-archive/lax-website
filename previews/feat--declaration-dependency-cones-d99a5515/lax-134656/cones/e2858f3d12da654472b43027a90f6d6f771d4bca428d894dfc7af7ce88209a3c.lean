-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.ModelTheory.Semantics

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
end

-- Lax485149.Problems
section
namespace Lax485149
end Lax485149

namespace Lax485149.Problems
end Lax485149.Problems

namespace Lax485149.Problems.DecisionProblem
end Lax485149.Problems.DecisionProblem

namespace Lax485149.Problems.DecisionProblem.ofPred
end Lax485149.Problems.DecisionProblem.ofPred
end

-- Lax134656.Qsat
section
namespace Lax134656.Qsat.QsatWins
end Lax134656.Qsat.QsatWins

namespace Lax134656.Qsat

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- The relation symbols of the language. -/
inductive qsatRel : ℕ → Type where
/-- `isVar x`: the element `x` is a quantified propositional variable. -/
  | isVar : qsatRel 1
/-- `allVar x`: the variable `x` is quantified universally. -/
  | allVar : qsatRel 1
/-- `prefixLt x y`: the variable `x` is quantified outside the variable
  `y`. -/
  | prefixLt : qsatRel 2
/-- `isClause c`: the element `c` is a clause of the matrix. -/
  | isClause : qsatRel 1
/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : qsatRel 2
/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : qsatRel 2
  deriving DecidableEq

/-- The relational vocabulary of fully quantified Boolean formulas: that of
CNF instances, together with the marks and the order describing the quantifier
prefix. -/
def qsat : FirstOrder.Language :=
  ⟨fun _ => Empty, qsatRel⟩

/-- `isVar x`: the element `x` is a quantified propositional variable. -/
abbrev qsIsVar : qsat.Relations 1 :=
  .isVar

/-- `prefixLt x y`: the variable `x` is quantified outside the variable
  `y`. -/
abbrev qsPrefixLt : qsat.Relations 2 :=
  .prefixLt

open FirstOrder

open Language Structure

section Reading

variable {A : Type} [qsat.Structure A]

/-- The element `x` is a quantified propositional variable. -/
def IsQVar (x : A) : Prop := RelMap qsIsVar ![x]

/-- The variable `x` is quantified outside the variable `y`. -/
def QPrec (x y : A) : Prop := RelMap qsPrefixLt ![x, y]

variable (A) in
/-- An instance is *well formed* when the quantifier prefix is a strict linear
order on the marked variables. Malformed instances are no-instances; the
condition is first-order, so the membership proof can check it. -/
structure QsatWf : Prop where
  /-- The prefix order only relates quantified variables. -/
  isVar_of_prec : ∀ x y : A, QPrec x y → IsQVar x ∧ IsQVar y
  /-- The prefix order is irreflexive. -/
  irrefl : ∀ x : A, ¬QPrec x x
  /-- The prefix order is transitive. -/
  trans : ∀ x y z : A, QPrec x y → QPrec y z → QPrec x z
  /-- The prefix order is total on the quantified variables. -/
  total : ∀ x y : A, IsQVar x → IsQVar y → x ≠ y → QPrec x y ∨ QPrec y x

end Reading

section Game

variable {A : Type} [qsat.Structure A]

end Game

section Problem

variable {A : Type} [qsat.Structure A]

end Problem

end Lax134656.Qsat
end
