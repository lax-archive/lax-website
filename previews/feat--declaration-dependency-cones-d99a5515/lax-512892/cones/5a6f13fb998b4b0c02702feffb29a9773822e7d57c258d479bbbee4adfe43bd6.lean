-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Basic

-- Lax512892.RelationalStructures
section
namespace Lax512892
end Lax512892

namespace Lax512892.RelationalStructures
end Lax512892.RelationalStructures

namespace Lax512892.RelationalStructures.Structure
end Lax512892.RelationalStructures.Structure

namespace Lax512892.RelationalStructures.Vocabulary
end Lax512892.RelationalStructures.Vocabulary
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
end Lax512892.Locality

namespace Lax512892.Locality.LocalFormula
end Lax512892.Locality.LocalFormula

namespace Lax512892.Locality.LocalTerm
end Lax512892.Locality.LocalTerm

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

namespace Lax512892.Locality.LocalTerm.anchor
end Lax512892.Locality.LocalTerm.anchor

namespace Lax512892.Locality.LocalTerm.bound
end Lax512892.Locality.LocalTerm.bound

namespace Lax512892.Locality.LocalTerm.const
end Lax512892.Locality.LocalTerm.const

namespace Lax512892.Locality.LocalTerm.eval
end Lax512892.Locality.LocalTerm.eval
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

namespace BasicLocalSentence

end BasicLocalSentence

namespace NormalForm

end NormalForm

end Lax512892.GaifmanNormalForm
end
