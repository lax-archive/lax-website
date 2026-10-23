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

/-- `allVar x`: the variable `x` is quantified universally. -/
abbrev qsAllVar : qsat.Relations 1 :=
  .allVar

/-- `prefixLt x y`: the variable `x` is quantified outside the variable
  `y`. -/
abbrev qsPrefixLt : qsat.Relations 2 :=
  .prefixLt

/-- `isClause c`: the element `c` is a clause of the matrix. -/
abbrev qsIsClause : qsat.Relations 1 :=
  .isClause

/-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
abbrev qsPosIn : qsat.Relations 2 :=
  .posIn

/-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
abbrev qsNegIn : qsat.Relations 2 :=
  .negIn

open FirstOrder

open Language Structure

section Reading

variable {A : Type} [qsat.Structure A]

/-- The element `x` is a quantified propositional variable. -/
def IsQVar (x : A) : Prop := RelMap qsIsVar ![x]

/-- The variable `x` is quantified universally. -/
def IsQAll (x : A) : Prop := RelMap qsAllVar ![x]

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

/-- The matrix: every clause contains a literal on a *quantified* variable that
the valuation `τ` makes true. Elements that are not clauses impose nothing,
exactly as for satisfiability; an occurrence on an element that the
prefix does not quantify is not a literal, so the matrix depends on `τ` only
through its values on the variables. -/
def QsatMatrix (τ : A → Prop) : Prop :=
  ∀ c : A, RelMap qsIsClause ![c] →
    ∃ x : A, IsQVar x ∧
      ((RelMap qsPosIn ![c, x] ∧ τ x) ∨ (RelMap qsNegIn ![c, x] ∧ ¬τ x))

/-- Adding a variable to the set of already-quantified ones. -/
def qAdd (D : A → Prop) (x : A) : A → Prop := fun y => y = x ∨ D y

/-- Giving the value `b` to the variable `x` in the valuation `τ`. -/
def qUpd (τ : A → Prop) (x : A) (b : Bool) : A → Prop :=
  fun y => (y = x ∧ b = true) ∨ (y ≠ x ∧ τ y)

/-- The variable `x` is the one the position `D` quantifies next: it is the
`prefixLt`-least variable that `D` does not contain. -/
def QLeast (D : A → Prop) (x : A) : Prop :=
  IsQVar x ∧ ¬D x ∧ ∀ y : A, IsQVar y → ¬D y → ¬QPrec y x

end Reading

section Game

variable {A : Type} [qsat.Structure A]

/-- **The quantifier game**: the existential player wins the position `(D, τ)`.
Either every variable is already quantified and the matrix holds, or the next
variable is existential and one of its two values wins, or it is universal and
both of its values win. -/
inductive QsatWins : (A → Prop) → (A → Prop) → Prop
  /-- Every variable has been quantified: the position is won exactly when the
  matrix holds. -/
  | leaf {D τ : A → Prop} (hD : ∀ x : A, IsQVar x → D x) (hm : QsatMatrix τ) : QsatWins D τ
  /-- The next variable is existential: the existential player picks a value
  winning the rest of the game. -/
  | ex {D τ : A → Prop} {x : A} (hx : QLeast D x) (hq : ¬IsQAll x) (b : Bool)
      (h : QsatWins (qAdd D x) (qUpd τ x b)) : QsatWins D τ
  /-- The next variable is universal: both values must win the rest of the
  game. -/
  | all {D τ : A → Prop} {x : A} (hx : QLeast D x) (hq : IsQAll x)
      (h : ∀ b : Bool, QsatWins (qAdd D x) (qUpd τ x b)) : QsatWins D τ

end Game

section Problem

variable {A : Type} [qsat.Structure A]

variable (A) in
/-- **The yes-instances of QSAT**: a well-formed instance whose quantified
formula is true, i.e., whose initial position – nothing quantified yet, the
empty valuation – is won by the existential player. -/
def QsatHolds : Prop :=
  QsatWf A ∧ QsatWins (fun _ : A => False) (fun _ : A => False)

end Problem

end Lax134656.Qsat
end
