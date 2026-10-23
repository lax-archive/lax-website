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

namespace Lax512892.Locality.LocalFormula.eq
end Lax512892.Locality.LocalFormula.eq

namespace Lax512892.Locality.LocalFormula.ex
end Lax512892.Locality.LocalFormula.ex

namespace Lax512892.Locality.LocalFormula.not
end Lax512892.Locality.LocalFormula.not

namespace Lax512892.Locality.LocalFormula.or
end Lax512892.Locality.LocalFormula.or

namespace Lax512892.Locality.LocalFormula.rel
end Lax512892.Locality.LocalFormula.rel

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

end LocalFormula

end Lax512892.Locality
end
