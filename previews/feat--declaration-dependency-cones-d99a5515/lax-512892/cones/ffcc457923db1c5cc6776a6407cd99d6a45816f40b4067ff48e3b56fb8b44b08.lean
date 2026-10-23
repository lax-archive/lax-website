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

end Vocabulary

end Lax512892.RelationalStructures
end
