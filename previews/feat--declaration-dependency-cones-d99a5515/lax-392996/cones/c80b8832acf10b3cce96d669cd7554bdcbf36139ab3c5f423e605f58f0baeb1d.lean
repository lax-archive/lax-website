-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Init
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

end Lax392996.Databases
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

-- Lax392996.MultisetSemantics
section
namespace Lax392996.MultisetSemantics.Query
end Lax392996.MultisetSemantics.Query

namespace Lax392996.MultisetSemantics.Relation
end Lax392996.MultisetSemantics.Relation

namespace Lax392996.MultisetSemantics.Query.evaluate
end Lax392996.MultisetSemantics.Query.evaluate

namespace Lax392996.MultisetSemantics

open Lax392996.Databases Lax392996.RelationalAlgebra

variable {T : Type} [ValueType T]

/-- Addition as a binary function, the fold of the `⊕`-sum performed by
the provenance aggregation `Query.ProvSum`. -/
def addFn (a b : T) := a + b

end Lax392996.MultisetSemantics
end
