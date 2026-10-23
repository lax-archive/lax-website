-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.Order.Basic

-- Lax895169.BitPredicate
section
namespace Lax895169.BitPredicate.prefixHolds
end Lax895169.BitPredicate.prefixHolds

namespace Lax895169.BitPredicate

/-- The rank of an element of a finite linear order: the number of its strict
predecessors. -/
noncomputable def orank {A : Type} [LinearOrder A] (z : A) : ℕ :=
  {y : A | y < z}.ncard

end Lax895169.BitPredicate
end

-- Lax904597.Problems
section
namespace Lax904597
end Lax904597

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Problems.DecisionProblem
end Lax904597.Problems.DecisionProblem
end

-- Lax895169.ArithmeticLogic
section
namespace Lax895169.ArithmeticLogic

open Lax895169.BitPredicate Lax904597.Problems

open FirstOrder

open FirstOrder.Language

/-- Relation symbols of the arithmetic vocabulary. -/
inductive arithRel : ℕ → Type
  /-- `le x y`: the rank of `x` is at most the rank of `y`, i.e., `x ≤ y`. -/
  | le : arithRel 2
  /-- `plus x y z`: the ranks satisfy `orank x + orank y = orank z`. -/
  | plus : arithRel 3
  /-- `times x y z`: the ranks satisfy `orank x * orank y = orank z`. -/
  | times : arithRel 3
  deriving DecidableEq

/-- The relational vocabulary of the numeric predicates: a linear order and the
graphs of addition and multiplication of ranks. Interpreted canonically on every
finite linear order by `arithStructure`. -/
def arith : Language :=
  ⟨fun _ => Empty, arithRel⟩

instance instIsRelationalArith : IsRelational arith := fun _ =>
  (inferInstance : IsEmpty Empty)

open FirstOrder

open Language Structure

section Structures

variable (A : Type) [LinearOrder A] [Finite A]

/-- **The numeric predicates of a finite linear order**: `≤` is the order, and
`plus`/`times` are the graphs of addition and multiplication of ranks. Both are
truncated: a value that is not the rank of an element of `A` is not related to
anything. -/
instance arithStructure : arith.Structure A where
  funMap f := isEmptyElim f
  RelMap {n} R :=
    match n, R with
    | _, .le => fun x => x 0 ≤ x 1
    | _, .plus => fun x => orank (x 0) + orank (x 1) = orank (x 2)
    | _, .times => fun x => orank (x 0) * orank (x 1) = orank (x 2)

end Structures

open FirstOrder

open Language

end Lax895169.ArithmeticLogic
end
