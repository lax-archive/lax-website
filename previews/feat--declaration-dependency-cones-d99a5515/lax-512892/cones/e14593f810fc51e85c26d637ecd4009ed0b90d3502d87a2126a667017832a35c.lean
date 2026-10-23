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

open Lax512892.RelationalStructures

/-- Terms over `σ` with `k` available variables. -/
inductive Term (σ : Vocabulary) (k : ℕ) : Type
  /-- A variable. -/
  | var (i : Fin k)
  /-- A constant of the vocabulary. -/
  | const (c : σ.Constant)

/-- First-order formulas over `σ` with `k` available free variables. -/
inductive Formula (σ : Vocabulary) : ℕ → Type
  /-- A relation atom. -/
  | rel {k : ℕ} (R : σ.Relation) (args : Fin (σ.arity R) → Term σ k) : Formula σ k
  /-- Equality of terms. -/
  | eq {k : ℕ} (left right : Term σ k) : Formula σ k
  /-- Negation. -/
  | not {k : ℕ} (φ : Formula σ k) : Formula σ k
  /-- Disjunction. -/
  | or {k : ℕ} (φ ψ : Formula σ k) : Formula σ k
  /-- Existential quantification, binding the new last variable. -/
  | ex {k : ℕ} (φ : Formula σ (k + 1)) : Formula σ k

namespace Term

/-- Interpretation of a term in a structure under an environment. -/
def eval {σ : Vocabulary} {M : Type*} {k : ℕ} (A : Structure σ M)
    (env : Fin k → M) : Term σ k → M
  | .var i => env i
  | .const c => A.constant c

end Term

namespace Formula

/-- Satisfaction of a formula in a structure under an environment for its free
variables. -/
def Sat {σ : Vocabulary} {M : Type*} (A : Structure σ M) :
    {k : ℕ} → Formula σ k → (Fin k → M) → Prop
  | _, .rel R args, env => A.relation R (fun i => (args i).eval A env)
  | _, .eq left right, env => left.eval A env = right.eval A env
  | _, .not φ, env => ¬ Sat A φ env
  | _, .or φ ψ, env => Sat A φ env ∨ Sat A ψ env
  | _, .ex φ, env => ∃ x : M, Sat A φ (Fin.snoc env x)

/-- The quantifier rank of a formula. -/
def quantifierRank {σ : Vocabulary} : {k : ℕ} → Formula σ k → ℕ
  | _, .rel _ _ => 0
  | _, .eq _ _ => 0
  | _, .not φ => quantifierRank φ
  | _, .or φ ψ => max (quantifierRank φ) (quantifierRank ψ)
  | _, .ex φ => quantifierRank φ + 1

end Formula

end Lax512892.FirstOrder
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

/-- The atoms occurring in a Boolean combination, with multiplicity. -/
def atoms {α : Type u} : BooleanCombination α → List α
  | .atom a => [a]
  | .truth => []
  | .not b => b.atoms
  | .and b c => b.atoms ++ c.atoms

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

/-- Every basic local sentence occurring in `nf` uses at most `bound`
witnesses. -/
def WitnessesBounded {σ : Vocabulary} {k : ℕ}
    (nf : NormalForm σ k) (bound : ℕ) : Prop :=
  ∀ basic : BasicLocalSentence σ nf.radius,
    Sum.inr basic ∈ nf.body.atoms → basic.witnessCount ≤ bound

/-- No local-formula atom occurs in `nf`. -/
def ContainsOnlyBasicSentences {σ : Vocabulary} {k : ℕ}
    (nf : NormalForm σ k) : Prop :=
  ∀ ψ : LocalFormula σ k nf.radius 0, Sum.inl ψ ∉ nf.body.atoms

end NormalForm

/-- **Gaifman's normal-form theorem.** There is a uniform transformation of
every first-order formula over `σ` into an equivalent Gaifman normal form. For
an input of quantifier rank `q` with `k` free variables, its common radius is at
most `7 ^ q`, each basic local sentence has at most `q + k` witnesses, and a
sentence is translated using basic local sentences only. Equivalence holds in
every finite `σ`-structure. -/
axiom gaifmanNormalForm (σ : Vocabulary) :
    ∃ translate : (k : ℕ) → Formula σ k → NormalForm σ k,
      ∀ (k : ℕ) (φ : Formula σ k),
        (translate k φ).radius ≤ 7 ^ φ.quantifierRank ∧
        (translate k φ).WitnessesBounded (φ.quantifierRank + k) ∧
        (k = 0 → (translate k φ).ContainsOnlyBasicSentences) ∧
        ∀ {M : Type} [Fintype M] (A : Structure σ M) (env : Fin k → M),
          φ.Sat A env ↔ (translate k φ).Sat A env

end Lax512892.GaifmanNormalForm
end
