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

/-- The finite type of constant symbols of `σ`. -/
abbrev Constant (σ : Vocabulary) := Fin σ.constantCount

end Vocabulary

end Lax512892.RelationalStructures
end

-- Lax512892.FirstOrder
section
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

namespace Term

end Term

namespace Formula

end Formula

end Lax512892.FirstOrder
end
