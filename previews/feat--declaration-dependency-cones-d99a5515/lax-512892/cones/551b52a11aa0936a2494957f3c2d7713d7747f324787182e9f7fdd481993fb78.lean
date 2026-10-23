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
