-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Lattice
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic.FinCases

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
end

-- Lax904597.SecondOrder
section
namespace Lax904597.SecondOrder.SORealize
end Lax904597.SecondOrder.SORealize

namespace Lax904597.SecondOrder.soLang
end Lax904597.SecondOrder.soLang

namespace Lax904597.SecondOrder

open FirstOrder FirstOrder.Language Lax904597.Problems

/-- A second-order quantifier block: finitely many relation variables, with
given arities. The index type is arbitrary rather than an initial segment of
`ℕ`, so that constructions on blocks can build their natural index types. -/
structure SOBlock : Type 1 where
  /-- The index type of the relation variables of the block. -/
  ι : Type
  /-- A block has finitely many relation variables. -/
  [ιFinite : Finite ι]
  /-- The arity of each relation variable. -/
  arity : ι → ℕ

attribute [instance] SOBlock.ιFinite

variable {L : Language.{0, 0}}

end Lax904597.SecondOrder
end

-- Lax624099.ValueInvention
section
namespace Lax624099.ValueInvention

open Lax904597.Problems Lax904597.SecondOrder

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the language marking the original elements inside an
extended universe. -/
inductive oldRel : ℕ → Type
  /-- `old x`: the element `x` comes from the original structure, i.e., it is
  not an invented value. -/
  | old : oldRel 1
  deriving DecidableEq

/-- The one-symbol relational language marking, inside a universe extended
with invented values, the elements of the original structure. -/
def oldMark : Language :=
  ⟨fun _ => Empty, oldRel⟩

instance instIsRelationalOldMark : IsRelational oldMark :=
  fun _ => ⟨fun f => Empty.elim f⟩

open FirstOrder

open Language Structure

section Extended

/-- The original elements of a universe extended by invented values. The
invented values are an arbitrary type, so that the same predicate reads an
extension by a *set* of them and not only by an initial segment. -/
def IsOld {A N : Type} : A ⊕ N → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- The interpretation of the marking predicate on the extended universe. -/
@[reducible]
def oldMarkStructure (A : Type) (m : ℕ) : oldMark.Structure (A ⊕ Fin m) where
  RelMap | .old => fun x => IsOld (x 0)

end Extended

section Definability

variable {L : Language.{0, 0}}

end Definability

end Lax624099.ValueInvention
end
