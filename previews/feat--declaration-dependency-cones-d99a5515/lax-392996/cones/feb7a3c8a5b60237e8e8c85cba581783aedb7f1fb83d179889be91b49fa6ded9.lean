-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Init
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.String.Basic
import Mathlib.Logic.Basic
import Mathlib.Order.Basic
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

end Lax392996.Databases
end

-- Lax392996.SemiringsWithMonus
section
namespace Lax392996
end Lax392996

namespace Lax392996.SemiringsWithMonus
end Lax392996.SemiringsWithMonus

namespace Lax392996.SemiringsWithMonus.HasAltLinearOrder
end Lax392996.SemiringsWithMonus.HasAltLinearOrder

namespace Lax392996.SemiringsWithMonus.SemiringWithMonus
end Lax392996.SemiringsWithMonus.SemiringWithMonus
end

-- Lax392996.AnnotatedDatabases
section
namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase
end Lax392996.AnnotatedDatabases.AnnotatedDatabase

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

namespace Lax392996.AnnotatedDatabases

open Lax392996.Databases Lax392996.SemiringsWithMonus

universe u

variable {T : Type} [ValueType T] {K : Type} [Zero K] {n : ℕ}

/-- An annotated tuple: a tuple paired with an annotation, ordered
lexicographically. -/
abbrev AnnotatedTuple (T : Type) (K : Type u) (n: ℕ) := Tuple T n ×ₗ K

/-- A `K`-relation of arity `arity`: a finite multiset of annotated tuples. -/
def AnnotatedRelation (T : Type) (K : Type u) (arity: ℕ) := Multiset (AnnotatedTuple T K arity)

end Lax392996.AnnotatedDatabases
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
namespace Lax392996.AnnotatedSemantics
end Lax392996.AnnotatedSemantics

namespace Lax392996.AnnotatedSemantics.Query
end Lax392996.AnnotatedSemantics.Query

namespace Lax392996.AnnotatedSemantics.Selection
end Lax392996.AnnotatedSemantics.Selection

namespace Lax392996.AnnotatedSemantics.Query.evaluateAnnotated
end Lax392996.AnnotatedSemantics.Query.evaluateAnnotated

namespace Lax392996.AnnotatedSemantics.Selection.evalDecidableAnnotated
end Lax392996.AnnotatedSemantics.Selection.evalDecidableAnnotated
end

-- Lax392996.BooleanFunctions
section
namespace Lax392996.BooleanFunctions

open Lax392996.SemiringsWithMonus

variable {X : Type}

/-- The type of Boolean functions over Boolean assignments to `X`:
`(X → Bool) → Bool` with pointwise operations. -/
def BoolFunc (X : Type) := (X → Bool) → Bool

end Lax392996.BooleanFunctions
end

-- Lax392996.MultisetSemantics
section
namespace Lax392996.MultisetSemantics
end Lax392996.MultisetSemantics

namespace Lax392996.MultisetSemantics.Query
end Lax392996.MultisetSemantics.Query

namespace Lax392996.MultisetSemantics.Relation
end Lax392996.MultisetSemantics.Relation

namespace Lax392996.MultisetSemantics.Query.evaluate
end Lax392996.MultisetSemantics.Query.evaluate
end

-- Lax392996.PersonnelExample
section
namespace Lax392996.PersonnelExample
end Lax392996.PersonnelExample
end

-- Lax392996.ProbabilisticDatabases
section
namespace Lax392996.ProbabilisticDatabases
end Lax392996.ProbabilisticDatabases

namespace Lax392996.ProbabilisticDatabases.AnnotatedDatabase
end Lax392996.ProbabilisticDatabases.AnnotatedDatabase

namespace Lax392996.ProbabilisticDatabases.ProbAssignment
end Lax392996.ProbabilisticDatabases.ProbAssignment
end

-- Lax392996.ProvenanceExample
section
namespace Lax392996.ProvenanceExample

open Lax392996.SemiringsWithMonus Lax392996.BooleanFunctions Lax392996.Databases

open Lax392996.AnnotatedDatabases Lax392996.RelationalAlgebra Lax392996.AnnotatedSemantics

open Lax392996.ProbabilisticDatabases Lax392996.PersonnelExample

/-- The variable `t_i`, as the Boolean function reading it off a valuation. -/
def t (i : Fin 7) : BoolFunc (Fin 7) := fun ν => ν i

/-- `Personnel` annotated: the tuple with id `i` carries `t_i`. -/
def personnelB : AnnotatedRelation String (BoolFunc (Fin 7)) 4 := Multiset.ofList [
  toLex (!["1", "Juma", "Director", "Nairobi"], t 0),
  toLex (!["2", "Paul", "Janitor", "Nairobi"], t 1),
  toLex (!["3", "David", "Analyst", "Paris"], t 2),
  toLex (!["4", "Ellen", "Field agent", "Beijing"], t 3),
  toLex (!["5", "Aaheli", "Double agent", "Paris"], t 4),
  toLex (!["6", "Nancy", "HR", "Paris"], t 5),
  toLex (!["7", "Jing", "Analyst", "Beijing"], t 6)]

end Lax392996.ProvenanceExample
end
