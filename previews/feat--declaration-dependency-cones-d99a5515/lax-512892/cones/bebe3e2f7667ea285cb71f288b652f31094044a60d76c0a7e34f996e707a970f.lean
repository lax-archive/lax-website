-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Basic

-- Lax512892.RelationalStructures
section
namespace Lax512892.RelationalStructures

/-- A finite relational vocabulary: a finite list of relation arities and a
finite number of constant symbols. -/
structure Vocabulary where
  /-- One arity for each relation symbol. -/
  relationArities : List ℕ
  /-- The number of constant symbols. -/
  constantCount : ℕ

namespace Vocabulary

/-- The finite type of relation symbols of `σ`. -/
abbrev Relation (σ : Vocabulary) := Fin σ.relationArities.length

/-- The arity of a relation symbol. -/
def arity (σ : Vocabulary) (R : σ.Relation) : ℕ :=
  σ.relationArities.get R

/-- The finite type of constant symbols of `σ`. -/
abbrev Constant (σ : Vocabulary) := Fin σ.constantCount

end Vocabulary

/-- An interpretation of the relational vocabulary `σ` on the carrier `M`. -/
structure Structure (σ : Vocabulary) (M : Type*) where
  /-- Interpretation of every relation symbol as a relation of its arity. -/
  relation : (R : σ.Relation) → (Fin (σ.arity R) → M) → Prop
  /-- Interpretation of every constant symbol. -/
  constant : σ.Constant → M

end Lax512892.RelationalStructures
end

-- Lax512892.FirstOrder
section
namespace Lax512892.FirstOrder
end Lax512892.FirstOrder

namespace Lax512892.FirstOrder.Formula
end Lax512892.FirstOrder.Formula

namespace Lax512892.FirstOrder.Term
end Lax512892.FirstOrder.Term

namespace Lax512892.FirstOrder.Formula.Sat
end Lax512892.FirstOrder.Formula.Sat

namespace Lax512892.FirstOrder.Formula.eq
end Lax512892.FirstOrder.Formula.eq

namespace Lax512892.FirstOrder.Formula.ex
end Lax512892.FirstOrder.Formula.ex

namespace Lax512892.FirstOrder.Formula.not
end Lax512892.FirstOrder.Formula.not

namespace Lax512892.FirstOrder.Formula.or
end Lax512892.FirstOrder.Formula.or

namespace Lax512892.FirstOrder.Formula.quantifierRank
end Lax512892.FirstOrder.Formula.quantifierRank

namespace Lax512892.FirstOrder.Formula.rel
end Lax512892.FirstOrder.Formula.rel

namespace Lax512892.FirstOrder.Term.const
end Lax512892.FirstOrder.Term.const

namespace Lax512892.FirstOrder.Term.eval
end Lax512892.FirstOrder.Term.eval

namespace Lax512892.FirstOrder.Term.var
end Lax512892.FirstOrder.Term.var
end

-- Lax512892.Locality
section
namespace Lax512892.Locality

open Lax512892.RelationalStructures Lax512892.FirstOrder

/-- Adjacency in the Gaifman graph of a relational structure. -/
def gaifmanAdjacent {σ : Vocabulary} {M : Type*} (A : Structure σ M) (a b : M) : Prop :=
  a ≠ b ∧
    ∃ (R : σ.Relation) (tuple : Fin (σ.arity R) → M),
      A.relation R tuple ∧
        ∃ i j : Fin (σ.arity R), i ≠ j ∧ tuple i = a ∧ tuple j = b

/-- `distanceAtMost A r a b` holds when a walk of at most `r` Gaifman edges
joins `a` to `b`. -/
def distanceAtMost {σ : Vocabulary} {M : Type*} (A : Structure σ M) :
    ℕ → M → M → Prop
  | 0, a, b => a = b
  | r + 1, a, b =>
      distanceAtMost A r a b ∨
        ∃ c : M, gaifmanAdjacent A a c ∧ distanceAtMost A r c b

/-- Membership in the union of the radius-`r` balls around the tuple `anchors`. -/
def inBallAround {σ : Vocabulary} {M : Type*} (A : Structure σ M)
    (r : ℕ) {k : ℕ} (anchors : Fin k → M) (x : M) : Prop :=
  ∃ i : Fin k, distanceAtMost A r (anchors i) x

/-- A term in a local formula, distinguishing the fixed anchor variables from
variables introduced by restricted quantifiers. -/
inductive LocalTerm (σ : Vocabulary) (anchorCount boundCount : ℕ) : Type
  /-- One of the fixed variables around which locality is measured. -/
  | anchor (i : Fin anchorCount)
  /-- A variable introduced by a restricted quantifier. -/
  | bound (i : Fin boundCount)
  /-- A constant of the vocabulary. -/
  | const (c : σ.Constant)

/-- Formulas whose quantifiers are all restricted to the radius-`r` ball around
the original `anchorCount` variables. -/
inductive LocalFormula (σ : Vocabulary) (anchorCount r : ℕ) : ℕ → Type
  /-- A relation atom. -/
  | rel {boundCount : ℕ} (R : σ.Relation)
      (args : Fin (σ.arity R) → LocalTerm σ anchorCount boundCount) :
      LocalFormula σ anchorCount r boundCount
  /-- Equality of local terms. -/
  | eq {boundCount : ℕ} (left right : LocalTerm σ anchorCount boundCount) :
      LocalFormula σ anchorCount r boundCount
  /-- Negation. -/
  | not {boundCount : ℕ} (φ : LocalFormula σ anchorCount r boundCount) :
      LocalFormula σ anchorCount r boundCount
  /-- Disjunction. -/
  | or {boundCount : ℕ} (φ ψ : LocalFormula σ anchorCount r boundCount) :
      LocalFormula σ anchorCount r boundCount
  /-- Existential quantification restricted to the radius-`r` ball around the
  original anchors. -/
  | ex {boundCount : ℕ} (φ : LocalFormula σ anchorCount r (boundCount + 1)) :
      LocalFormula σ anchorCount r boundCount

namespace LocalTerm

/-- Interpretation of a term occurring in a local formula. -/
def eval {σ : Vocabulary} {M : Type*} {anchorCount boundCount : ℕ}
    (A : Structure σ M)
    (anchors : Fin anchorCount → M) (bound : Fin boundCount → M) :
    LocalTerm σ anchorCount boundCount → M
  | .anchor i => anchors i
  | .bound i => bound i
  | .const c => A.constant c

end LocalTerm

namespace LocalFormula

/-- Satisfaction for a syntactically local formula. Every existential witness
is required to lie in the fixed neighbourhood of the anchor tuple. -/
def Sat {σ : Vocabulary} {M : Type*} {anchorCount r : ℕ}
    (A : Structure σ M)
    (anchors : Fin anchorCount → M) :
    {boundCount : ℕ} → LocalFormula σ anchorCount r boundCount →
      (Fin boundCount → M) → Prop
  | _, .rel R args, bound =>
      A.relation R (fun i => (args i).eval A anchors bound)
  | _, .eq left right, bound =>
      left.eval A anchors bound = right.eval A anchors bound
  | _, .not φ, bound => ¬ Sat A anchors φ bound
  | _, .or φ ψ, bound => Sat A anchors φ bound ∨ Sat A anchors ψ bound
  | _, .ex φ, bound =>
      ∃ x : M, inBallAround A r anchors x ∧ Sat A anchors φ (Fin.snoc bound x)

end LocalFormula

end Lax512892.Locality
end

-- Lax512892.GaifmanNormalForm
section
namespace Lax512892.GaifmanNormalForm

open Lax512892.RelationalStructures Lax512892.FirstOrder Lax512892.Locality

universe u

/-- Boolean combinations of atoms of type `α`. -/
inductive BooleanCombination (α : Type u) : Type u
  /-- An atomic constituent. -/
  | atom (a : α)
  /-- Truth, serving also as the empty Boolean combination. -/
  | truth
  /-- Negation. -/
  | not (b : BooleanCombination α)
  /-- Conjunction. -/
  | and (b c : BooleanCombination α)

namespace BooleanCombination

/-- Evaluation of a Boolean combination from an interpretation of its atoms. -/
def eval {α : Type u} (value : α → Prop) : BooleanCombination α → Prop
  | .atom a => value a
  | .truth => True
  | .not b => ¬ b.eval value
  | .and b c => b.eval value ∧ c.eval value

end BooleanCombination

/-- A basic local sentence at radius `r`: `witnessCount` pairwise far-apart
witnesses all satisfy the same one-variable local formula `property`. -/
structure BasicLocalSentence (σ : Vocabulary) (r : ℕ) where
  /-- The number of witnesses. -/
  witnessCount : ℕ
  /-- The uniform local property required of every witness. -/
  property : LocalFormula σ 1 r 0

namespace BasicLocalSentence

/-- Semantics of a basic local sentence. -/
def Sat {σ : Vocabulary} {M : Type*} {r : ℕ} (A : Structure σ M)
    (β : BasicLocalSentence σ r) : Prop :=
  ∃ witnesses : Fin β.witnessCount → M,
    (∀ i, β.property.Sat A (fun _ => witnesses i) Fin.elim0) ∧
      ∀ i j, i ≠ j →
        ¬ distanceAtMost A (2 * r) (witnesses i) (witnesses j)

end BasicLocalSentence

/-- A Gaifman normal form for a formula with `k` free variables. All its atoms
share the stored locality radius. -/
structure NormalForm (σ : Vocabulary) (k : ℕ) where
  /-- The common locality radius. -/
  radius : ℕ
  /-- A Boolean combination of local formulas and basic local sentences. -/
  body : BooleanCombination
    (LocalFormula σ k radius 0 ⊕ BasicLocalSentence σ radius)

namespace NormalForm

/-- Satisfaction of a normal form under an environment for its free variables. -/
def Sat {σ : Vocabulary} {M : Type*} {k : ℕ} (A : Structure σ M)
    (env : Fin k → M) (nf : NormalForm σ k) : Prop :=
  nf.body.eval (Sum.elim
    (fun ψ => ψ.Sat A env Fin.elim0)
    (fun basic => basic.Sat A))

end NormalForm

end Lax512892.GaifmanNormalForm
end
