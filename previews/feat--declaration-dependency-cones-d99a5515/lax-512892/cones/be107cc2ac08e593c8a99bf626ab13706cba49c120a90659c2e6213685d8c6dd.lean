-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Basic

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
namespace Lax512892.Locality.distanceAtMost
end Lax512892.Locality.distanceAtMost

namespace Lax512892.Locality.LocalFormula.Sat
end Lax512892.Locality.LocalFormula.Sat

namespace Lax512892.Locality.LocalTerm.eval
end Lax512892.Locality.LocalTerm.eval

namespace Lax512892.Locality

open Lax512892.RelationalStructures Lax512892.FirstOrder

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

end LocalTerm

namespace LocalFormula

end LocalFormula

end Lax512892.Locality
end

-- Lax512892.GaifmanNormalForm
section
namespace Lax512892.GaifmanNormalForm.BooleanCombination.and
end Lax512892.GaifmanNormalForm.BooleanCombination.and

namespace Lax512892.GaifmanNormalForm.BooleanCombination.atom
end Lax512892.GaifmanNormalForm.BooleanCombination.atom

namespace Lax512892.GaifmanNormalForm.BooleanCombination.eval
end Lax512892.GaifmanNormalForm.BooleanCombination.eval

namespace Lax512892.GaifmanNormalForm.BooleanCombination.not
end Lax512892.GaifmanNormalForm.BooleanCombination.not

namespace Lax512892.GaifmanNormalForm.BooleanCombination.truth
end Lax512892.GaifmanNormalForm.BooleanCombination.truth

namespace Lax512892.GaifmanNormalForm

open Lax512892.RelationalStructures Lax512892.FirstOrder Lax512892.Locality

universe u

namespace BooleanCombination

end BooleanCombination

/-- A basic local sentence at radius `r`: `witnessCount` pairwise far-apart
witnesses all satisfy the same one-variable local formula `property`. -/
structure BasicLocalSentence (σ : Vocabulary) (r : ℕ) where
  /-- The number of witnesses. -/
  witnessCount : ℕ
  /-- The uniform local property required of every witness. -/
  property : LocalFormula σ 1 r 0

namespace BasicLocalSentence

end BasicLocalSentence

namespace NormalForm

end NormalForm

end Lax512892.GaifmanNormalForm
end
