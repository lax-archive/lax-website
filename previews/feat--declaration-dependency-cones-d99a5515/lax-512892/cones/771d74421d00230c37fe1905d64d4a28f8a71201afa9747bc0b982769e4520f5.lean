-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic

-- Lax512892.RelationalStructures
section
namespace Lax512892.RelationalStructures.Structure
end Lax512892.RelationalStructures.Structure

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

end Lax512892.RelationalStructures
end

-- Lax512892.FirstOrder
section
namespace Lax512892.FirstOrder.Formula.Sat
end Lax512892.FirstOrder.Formula.Sat

namespace Lax512892.FirstOrder.Term.eval
end Lax512892.FirstOrder.Term.eval

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

end Term

namespace Formula

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
