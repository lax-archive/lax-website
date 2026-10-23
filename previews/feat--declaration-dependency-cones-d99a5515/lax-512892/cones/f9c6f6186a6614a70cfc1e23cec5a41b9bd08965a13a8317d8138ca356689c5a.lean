-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic

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
namespace Lax512892.FirstOrder.Formula.quantifierRank
end Lax512892.FirstOrder.Formula.quantifierRank

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

end Formula

end Lax512892.FirstOrder
end
