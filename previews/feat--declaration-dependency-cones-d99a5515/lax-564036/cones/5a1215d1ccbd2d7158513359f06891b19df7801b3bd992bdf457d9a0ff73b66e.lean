-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.ModelTheory.Semantics

-- Lax904597.Problems
section
namespace Lax904597.Problems

open FirstOrder FirstOrder.Language

/-- A decision problem: an isomorphism-closed property of `L`-structures,
whose yes-instances are the `L`-structures satisfying it. -/
structure DecisionProblem (L : Language.{0, 0}) [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L : Language.{0, 0}} [L.IsRelational]

end DecisionProblem

end Lax904597.Problems
end

-- Lax485149.Problems
section
namespace Lax485149.Problems

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- The decision problem whose yes-instances are the structures isomorphic to
one satisfying `P`. -/
def DecisionProblem.ofPred {L : Language.{0, 0}} [L.IsRelational]
    (P : ∀ (A : Type) [L.Structure A], Prop) : DecisionProblem L where
  Holds := fun A _ => ∃ (B : Type) (i : L.Structure B) (_ : @Language.Equiv L B A i _), @P B i
  iso_invariant := fun e =>
    ⟨fun ⟨B, i, f, h⟩ => ⟨B, i, e.comp f, h⟩, fun ⟨B, i, f, h⟩ => ⟨B, i, e.symm.comp f, h⟩⟩

end Lax485149.Problems
end

-- Lax564036.QuantifiedBooleanFormulas
section
namespace Lax564036.QuantifiedBooleanFormulas

open Lax904597.Problems Lax485149.Problems

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language of quantified Boolean formulas with `k`
quantifier blocks. -/
inductive qbfRel (k : ℕ) : ℕ → Type
  /-- `isClause c`: the element `c` is a clause (a term, for a disjunctive
  matrix). -/
  | isClause : qbfRel k 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  | posIn : qbfRel k 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  | negIn : qbfRel k 2
  /-- `block i x`: the variable `x` belongs to the `i`-th quantifier block. -/
  | block : Fin k → qbfRel k 1
  deriving DecidableEq

/-- The relational vocabulary of quantified Boolean formulas with `k`
quantifier blocks: that of CNF instances, together with `k` unary predicates
marking the variables of each quantifier block. -/
def qbf (k : ℕ) : Language :=
  ⟨fun _ => Empty, qbfRel k⟩

instance instIsRelationalQbf (k : ℕ) : IsRelational (qbf k) :=
  fun _ => ⟨fun f => Empty.elim f⟩

variable {k : ℕ}

/-- The symbol for “is a clause”. -/
abbrev qbfIsClause : (qbf k).Relations 1 := .isClause

/-- The symbol for “occurs positively in”. -/
abbrev qbfPosIn : (qbf k).Relations 2 := .posIn

/-- The symbol for “occurs negatively in”. -/
abbrev qbfNegIn : (qbf k).Relations 2 := .negIn

/-- The symbol marking the variables of the `i`-th quantifier block. -/
abbrev qbfBlock (i : Fin k) : (qbf k).Relations 1 := .block i

open FirstOrder

open Language Structure

/-- Alternating quantification over `k` truth assignments on `A`: the
assignment of index `0` is quantified outermost, existentially if `pol` is
`true`, and the polarities alternate inwards. -/
def altQuant (A : Type) : ∀ (k : ℕ), ((Fin k → A → Prop) → Prop) → Bool → Prop
  | 0, P, _ => P Fin.elim0
  | k + 1, P, true => ∃ ν : A → Prop, altQuant A k (fun νs => P (Fin.cons ν νs)) false
  | k + 1, P, false => ∀ ν : A → Prop, altQuant A k (fun νs => P (Fin.cons ν νs)) true

section Matrix

variable {k : ℕ} {A : Type} [(qbf k).Structure A]

/-- The truth value of the variable `x` under a tuple of block assignments:
`x` is true when some block marking it assigns it the value true. (In a
well-formed instance the block marks partition the variables, so exactly one
assignment is consulted.) -/
def qbfVal (νs : Fin k → A → Prop) (x : A) : Prop :=
  ∃ i : Fin k, RelMap (qbfBlock i) ![x] ∧ νs i x

/-- Conjunctive satisfaction, with the sign of every literal flipped when
`swap` is `true`: every clause then has to contain a literal that the block
assignments make *false*. -/
def CnfSatWith (swap : Bool) (νs : Fin k → A → Prop) : Prop :=
  ∀ c : A, RelMap (qbfIsClause (k := k)) ![c] →
    ∃ x : A,
      (RelMap (if swap then qbfNegIn (k := k) else qbfPosIn (k := k)) ![c, x] ∧ qbfVal νs x) ∨
      (RelMap (if swap then qbfPosIn (k := k) else qbfNegIn (k := k)) ![c, x] ∧ ¬qbfVal νs x)

/-- The conjunctive matrix: every clause contains a literal made true by the
block assignments. -/
abbrev CnfSat (νs : Fin k → A → Prop) : Prop := CnfSatWith false νs

/-- The disjunctive matrix: some term has all of its literals made true by the
block assignments. -/
def DnfSat (νs : Fin k → A → Prop) : Prop :=
  ∃ c : A, RelMap (qbfIsClause (k := k)) ![c] ∧
    ∀ x : A, (RelMap (qbfPosIn (k := k)) ![c, x] → qbfVal νs x) ∧
      (RelMap (qbfNegIn (k := k)) ![c, x] → ¬qbfVal νs x)

/-- The matrix of a quantified Boolean formula: conjunctive when `cnf` is
`true`, disjunctive when it is `false`. -/
def QbfMatrix (cnf : Bool) (νs : Fin k → A → Prop) : Prop :=
  match cnf with
  | true => CnfSat νs
  | false => DnfSat νs

end Matrix

/-- Quantified Boolean formulas with `k` alternating quantifier blocks: the
prefix starts with an existential block when `start` is `true`, and the matrix
is conjunctive when `cnf` is `true`. -/
def QbfProblem (k : ℕ) (start cnf : Bool) : DecisionProblem (qbf k) :=
  DecisionProblem.ofPred fun A _ => altQuant A k (fun νs => QbfMatrix cnf νs) start

end Lax564036.QuantifiedBooleanFormulas
end
