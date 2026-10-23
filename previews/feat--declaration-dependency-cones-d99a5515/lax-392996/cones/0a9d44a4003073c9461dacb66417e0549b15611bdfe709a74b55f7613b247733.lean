-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Init
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Basic
import Mathlib.Order.Defs.LinearOrder

-- Lax392996.Databases
section
namespace Lax392996.Databases.Database
end Lax392996.Databases.Database

namespace Lax392996.Databases.Relation
end Lax392996.Databases.Relation

namespace Lax392996.Databases.instHMulRelationHAddNat
end Lax392996.Databases.instHMulRelationHAddNat

namespace Lax392996.Databases.instLinearOrderTuple
end Lax392996.Databases.instLinearOrderTuple

namespace Lax392996.Databases.Database.find
end Lax392996.Databases.Database.find

namespace Lax392996.Databases

/-- The values of a database: a linearly ordered type with a zero, an
addition, a subtraction and a multiplication, the arithmetic of terms. -/
class ValueType (T : Type) extends Zero T, AddCommSemigroup T, Sub T, Mul T, LinearOrder T

variable {T : Type} [ValueType T] {n m : ℕ}

/-- A tuple of arity `n` over `T`. -/
def Tuple (T : Type) (n: ℕ) := Fin n → T

instance instDecidableEqTuple [DecidableEq T] : DecidableEq (Tuple T n) := by
  show DecidableEq (Fin n → T)
  infer_instance

end Lax392996.Databases
end

-- Lax392996.SemiringsWithMonus
section
namespace Lax392996.SemiringsWithMonus.HasAltLinearOrder
end Lax392996.SemiringsWithMonus.HasAltLinearOrder

universe u

namespace Lax392996.SemiringsWithMonus

/-- A `SemiringWithMonus` is a naturally ordered semiring
with a monus operation that is compatible with the natural order.
The semiring is not required to be commutative.

In addition to monus, the class carries a `δ : α → α` operator subject
to three axioms (`delta_zero`, `delta_natCast_pos`, and
`delta_absorb`). This is the duplicate-eliminating support
operator used to interpret aggregation in the framework of
[Amsterdamer, Deutch & Tannen, *Provenance for aggregate queries*][amsterdamer2011aggregate]. -/
class SemiringWithMonus (α : Type)
  extends Semiring α, PartialOrder α, IsOrderedAddMonoid α, CanonicallyOrderedAdd α, Sub α where
  monus_spec : ∀ a b c : α, a - b ≤ c ↔ a ≤ b + c
  /-- Duplicate-eliminating support operator. Sends `0` to `0` and any
  positive integer iterate of `1` to `1`. -/
  delta : α → α
  /-- `δ` sends `0` to `0`. -/
  delta_zero : delta 0 = 0
  /-- `δ` sends every positive integer iterate of `1` (i.e., every
  positive natural-number cast) to `1`. -/
  delta_natCast_pos : ∀ {n : ℕ}, 0 < n → delta ((n : α)) = 1
  /-- A δ-guard is absorbed by any multiple of one of its summands:
  `a ⊗ δ(a ⊕ b) = a`. This is what makes a group-existence factor
  redundant next to any provenance that already contains an occurrence
  of the group: `δ` acts as “the group exists” and nothing more. -/
  delta_absorb : ∀ (a b : α), a * delta (a + b) = a

end Lax392996.SemiringsWithMonus
end

-- Lax392996.AnnotatedDatabases
section
namespace Lax392996.AnnotatedDatabases
end Lax392996.AnnotatedDatabases

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase
end Lax392996.AnnotatedDatabases.AnnotatedDatabase

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation
end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedTuple
end Lax392996.AnnotatedDatabases.AnnotatedTuple

namespace Lax392996.AnnotatedDatabases.Tuple
end Lax392996.AnnotatedDatabases.Tuple

namespace Lax392996.AnnotatedDatabases.instValueTypeSumOfHasAltLinearOrderOfSemiringWithMonus
end Lax392996.AnnotatedDatabases.instValueTypeSumOfHasAltLinearOrderOfSemiringWithMonus

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase.find
end Lax392996.AnnotatedDatabases.AnnotatedDatabase.find

namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase.toComposite
end Lax392996.AnnotatedDatabases.AnnotatedDatabase.toComposite

namespace Lax392996.AnnotatedDatabases.Tuple.fromComposite
end Lax392996.AnnotatedDatabases.Tuple.fromComposite
end

-- Lax392996.RelationalAlgebra
section
namespace Lax392996.RelationalAlgebra
end Lax392996.RelationalAlgebra

namespace Lax392996.RelationalAlgebra.BoolTerm
end Lax392996.RelationalAlgebra.BoolTerm

namespace Lax392996.RelationalAlgebra.CompOp
end Lax392996.RelationalAlgebra.CompOp

namespace Lax392996.RelationalAlgebra.Query
end Lax392996.RelationalAlgebra.Query

namespace Lax392996.RelationalAlgebra.Selection
end Lax392996.RelationalAlgebra.Selection

namespace Lax392996.RelationalAlgebra.Term
end Lax392996.RelationalAlgebra.Term

namespace Lax392996.RelationalAlgebra.BoolTerm.EQ
end Lax392996.RelationalAlgebra.BoolTerm.EQ

namespace Lax392996.RelationalAlgebra.BoolTerm.GE
end Lax392996.RelationalAlgebra.BoolTerm.GE

namespace Lax392996.RelationalAlgebra.BoolTerm.GT
end Lax392996.RelationalAlgebra.BoolTerm.GT

namespace Lax392996.RelationalAlgebra.BoolTerm.LE
end Lax392996.RelationalAlgebra.BoolTerm.LE

namespace Lax392996.RelationalAlgebra.BoolTerm.LT
end Lax392996.RelationalAlgebra.BoolTerm.LT

namespace Lax392996.RelationalAlgebra.BoolTerm.NE
end Lax392996.RelationalAlgebra.BoolTerm.NE

namespace Lax392996.RelationalAlgebra.BoolTerm.castToAnnotatedTuple
end Lax392996.RelationalAlgebra.BoolTerm.castToAnnotatedTuple

namespace Lax392996.RelationalAlgebra.CompOp.eq
end Lax392996.RelationalAlgebra.CompOp.eq

namespace Lax392996.RelationalAlgebra.CompOp.eval
end Lax392996.RelationalAlgebra.CompOp.eval

namespace Lax392996.RelationalAlgebra.CompOp.ge
end Lax392996.RelationalAlgebra.CompOp.ge

namespace Lax392996.RelationalAlgebra.CompOp.gt
end Lax392996.RelationalAlgebra.CompOp.gt

namespace Lax392996.RelationalAlgebra.CompOp.le
end Lax392996.RelationalAlgebra.CompOp.le

namespace Lax392996.RelationalAlgebra.CompOp.lt
end Lax392996.RelationalAlgebra.CompOp.lt

namespace Lax392996.RelationalAlgebra.CompOp.ne
end Lax392996.RelationalAlgebra.CompOp.ne

namespace Lax392996.RelationalAlgebra.Query.Dedup
end Lax392996.RelationalAlgebra.Query.Dedup

namespace Lax392996.RelationalAlgebra.Query.Diff
end Lax392996.RelationalAlgebra.Query.Diff

namespace Lax392996.RelationalAlgebra.Query.Having
end Lax392996.RelationalAlgebra.Query.Having

namespace Lax392996.RelationalAlgebra.Query.Prod
end Lax392996.RelationalAlgebra.Query.Prod

namespace Lax392996.RelationalAlgebra.Query.Proj
end Lax392996.RelationalAlgebra.Query.Proj

namespace Lax392996.RelationalAlgebra.Query.ProvSum
end Lax392996.RelationalAlgebra.Query.ProvSum

namespace Lax392996.RelationalAlgebra.Query.Rel
end Lax392996.RelationalAlgebra.Query.Rel

namespace Lax392996.RelationalAlgebra.Query.Sel
end Lax392996.RelationalAlgebra.Query.Sel

namespace Lax392996.RelationalAlgebra.Query.Sum
end Lax392996.RelationalAlgebra.Query.Sum

namespace Lax392996.RelationalAlgebra.Query.source
end Lax392996.RelationalAlgebra.Query.source

namespace Lax392996.RelationalAlgebra.Selection.And
end Lax392996.RelationalAlgebra.Selection.And

namespace Lax392996.RelationalAlgebra.Selection.BT
end Lax392996.RelationalAlgebra.Selection.BT

namespace Lax392996.RelationalAlgebra.Selection.Not
end Lax392996.RelationalAlgebra.Selection.Not

namespace Lax392996.RelationalAlgebra.Selection.Or
end Lax392996.RelationalAlgebra.Selection.Or

namespace Lax392996.RelationalAlgebra.Selection.True
end Lax392996.RelationalAlgebra.Selection.True

namespace Lax392996.RelationalAlgebra.Selection.castToAnnotatedTuple
end Lax392996.RelationalAlgebra.Selection.castToAnnotatedTuple

namespace Lax392996.RelationalAlgebra.Selection.evalDecidable
end Lax392996.RelationalAlgebra.Selection.evalDecidable

namespace Lax392996.RelationalAlgebra.Term.add
end Lax392996.RelationalAlgebra.Term.add

namespace Lax392996.RelationalAlgebra.Term.castToAnnotatedTuple
end Lax392996.RelationalAlgebra.Term.castToAnnotatedTuple

namespace Lax392996.RelationalAlgebra.Term.const
end Lax392996.RelationalAlgebra.Term.const

namespace Lax392996.RelationalAlgebra.Term.index
end Lax392996.RelationalAlgebra.Term.index

namespace Lax392996.RelationalAlgebra.Term.mul
end Lax392996.RelationalAlgebra.Term.mul

namespace Lax392996.RelationalAlgebra.Term.sub
end Lax392996.RelationalAlgebra.Term.sub
end

-- Lax392996.AnnotatedSemantics
section
namespace Lax392996.AnnotatedSemantics.Query
end Lax392996.AnnotatedSemantics.Query

namespace Lax392996.AnnotatedSemantics.Selection
end Lax392996.AnnotatedSemantics.Selection

namespace Lax392996.AnnotatedSemantics.Query.evaluateAnnotated
end Lax392996.AnnotatedSemantics.Query.evaluateAnnotated

namespace Lax392996.AnnotatedSemantics.Selection.evalDecidableAnnotated
end Lax392996.AnnotatedSemantics.Selection.evalDecidableAnnotated

namespace Lax392996.AnnotatedSemantics

open Lax392996.SemiringsWithMonus Lax392996.Databases Lax392996.AnnotatedDatabases

open Lax392996.RelationalAlgebra

variable {T : Type} [ValueType T]

variable {K : Type} [SemiringWithMonus K]

/-- The `⊕`-sum of the annotations of the copies of the data part `u` in an
annotated relation. -/
def annotationSum {n : ℕ} (r : Multiset (Tuple T n × K)) (u : Tuple T n) : K :=
  (Multiset.map Prod.snd
    (@Multiset.filter _ (fun p : Tuple T n × K => p.1 = u)
      (fun p => instDecidableEqTuple p.1 u) r)).sum

/-- Grouping of annotated tuples by their data part: each distinct data
part once, with the `⊕`-sum of the annotations of its copies. -/
def groupByKey {n : ℕ} (r : Multiset (Tuple T n × K)) : Multiset (Tuple T n × K) :=
  Multiset.map (fun u => (u, annotationSum r u)) (Multiset.dedup (Multiset.map Prod.fst r))

end Lax392996.AnnotatedSemantics
end
