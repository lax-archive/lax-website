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

namespace Lax512892.Locality.LocalTerm.anchor
end Lax512892.Locality.LocalTerm.anchor

namespace Lax512892.Locality.LocalTerm.bound
end Lax512892.Locality.LocalTerm.bound

namespace Lax512892.Locality.LocalTerm.const
end Lax512892.Locality.LocalTerm.const

namespace Lax512892.Locality.LocalTerm.eval
end Lax512892.Locality.LocalTerm.eval

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

namespace LocalTerm

end LocalTerm

namespace LocalFormula

end LocalFormula

end Lax512892.Locality
end
