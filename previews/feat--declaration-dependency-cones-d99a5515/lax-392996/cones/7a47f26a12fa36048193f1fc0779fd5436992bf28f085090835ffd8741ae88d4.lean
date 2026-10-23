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

/-- A tuple of arity `n` over `T`. -/
def Tuple (T : Type) (n: ℕ) := Fin n → T

end Lax392996.Databases
end

-- Lax392996.RelationalAlgebra
section
namespace Lax392996.RelationalAlgebra.CompOp
end Lax392996.RelationalAlgebra.CompOp

namespace Lax392996.RelationalAlgebra.Query
end Lax392996.RelationalAlgebra.Query

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

namespace Lax392996.RelationalAlgebra

open Lax392996.Databases

universe u v

variable {T : Type} [ValueType T]

/-- A term over a tuple of arity `n`: a constant, an attribute, or an
arithmetic combination. -/
inductive Term (T : Sort u) (n : ℕ) where
| const : T → Term T n
| index : Fin n → Term T n
| add : Term T n → Term T n → Term T n
| sub : Term T n → Term T n → Term T n
| mul : Term T n → Term T n → Term T n

/-- A term read on the composite tuple: constants become data values,
attributes keep their index, the annotation column being the last one. -/
def Term.castToAnnotatedTuple {n : ℕ} {K : Type v} (t: Term T n) : Term (T⊕K) (n+1) := match t with
| Term.const c => Term.const (Sum.inl c)
| Term.index k => Term.index (k.castLT (k.val_lt_of_le (Nat.le_add_right n 1)))
| Term.add t₁ t₂ => Term.add t₁.castToAnnotatedTuple t₂.castToAnnotatedTuple
| Term.sub t₁ t₂ => Term.sub t₁.castToAnnotatedTuple t₂.castToAnnotatedTuple
| Term.mul t₁ t₂ => Term.mul t₁.castToAnnotatedTuple t₂.castToAnnotatedTuple

/-- The value of a term on a tuple. -/
def Term.eval {n : ℕ} (term: Term T n) (tuple: Tuple T n) := match term with
  | Term.const a => a
  | Term.index k => tuple k
  | Term.add t₁ t₂ => (t₁.eval tuple) + (t₂.eval tuple)
  | Term.sub t₁ t₂ => (t₁.eval tuple) - (t₂.eval tuple)
  | Term.mul t₁ t₂ => (t₁.eval tuple) * (t₂.eval tuple)

/-- A comparison between two terms. -/
inductive BoolTerm (T : Sort u) (n: ℕ) where
| EQ : Term T n → Term T n → BoolTerm T n
| NE : Term T n → Term T n → BoolTerm T n
| LE : Term T n → Term T n → BoolTerm T n
| LT : Term T n → Term T n → BoolTerm T n
| GE : Term T n → Term T n → BoolTerm T n
| GT : Term T n → Term T n → BoolTerm T n

/-- A comparison read on the composite tuple. -/
def BoolTerm.castToAnnotatedTuple {n : ℕ} {K : Type v} (bt: BoolTerm T n): BoolTerm (T⊕K) (n+1) :=
  match bt with
  | BoolTerm.EQ a b => BoolTerm.EQ a.castToAnnotatedTuple b.castToAnnotatedTuple
  | BoolTerm.NE a b => BoolTerm.NE a.castToAnnotatedTuple b.castToAnnotatedTuple
  | BoolTerm.LE a b => BoolTerm.LE a.castToAnnotatedTuple b.castToAnnotatedTuple
  | BoolTerm.LT a b => BoolTerm.LT a.castToAnnotatedTuple b.castToAnnotatedTuple
  | BoolTerm.GE a b => BoolTerm.GE a.castToAnnotatedTuple b.castToAnnotatedTuple
  | BoolTerm.GT a b => BoolTerm.GT a.castToAnnotatedTuple b.castToAnnotatedTuple

/-- The truth of a comparison on a tuple. -/
def BoolTerm.eval {n : ℕ} (φ: BoolTerm T n) (tuple: Tuple T n) := match φ with
| BoolTerm.EQ t₁ t₂ => (t₁.eval tuple) = (t₂.eval tuple)
| BoolTerm.NE t₁ t₂ => (t₁.eval tuple) ≠ (t₂.eval tuple)
| BoolTerm.LE t₁ t₂ => (t₁.eval tuple) ≤ (t₂.eval tuple)
| BoolTerm.LT t₁ t₂ => (t₁.eval tuple) < (t₂.eval tuple)
| BoolTerm.GE t₁ t₂ => (t₁.eval tuple) ≥ (t₂.eval tuple)
| BoolTerm.GT t₁ t₂ => (t₁.eval tuple) > (t₂.eval tuple)

@[reducible] def BoolTerm.evalDecidable {n : ℕ} (φ: BoolTerm T n) : DecidablePred φ.eval :=
  λ t => by
    cases φ with
    | EQ x y => simp [BoolTerm.eval]; exact (inferInstance : Decidable (x.eval t = y.eval t))
    | NE x y => simp [BoolTerm.eval]; exact (inferInstance : Decidable (x.eval t ≠ y.eval t))
    | LE x y => simp [BoolTerm.eval]; exact (inferInstance : Decidable (x.eval t ≤ y.eval t))
    | LT x y => simp [BoolTerm.eval]; exact (inferInstance : Decidable (x.eval t < y.eval t))
    | GE x y => simp [BoolTerm.eval]; exact (inferInstance : Decidable (y.eval t ≤ x.eval t))
    | GT x y => simp [BoolTerm.eval]; exact (inferInstance : Decidable (y.eval t < x.eval t))

/-- A selection condition: a Boolean combination of comparisons. -/
inductive Selection (T : Sort u) (n: ℕ) where
| BT   : BoolTerm T n   → Selection T n
| Not  : Selection T n → Selection T n
| And  : Selection T n → Selection T n → Selection T n
| Or   : Selection T n → Selection T n → Selection T n
| True : Selection T n

/-- A selection condition read on the composite tuple. -/
def Selection.castToAnnotatedTuple {n : ℕ} {K : Type v} (f: Selection T n): Selection (T⊕K) (n+1) := match f with
| Selection.BT  t     => Selection.BT t.castToAnnotatedTuple
| Selection.Not φ     => Selection.Not φ.castToAnnotatedTuple
| Selection.And φ₁ φ₂ => Selection.And φ₁.castToAnnotatedTuple φ₂.castToAnnotatedTuple
| Selection.Or  φ₁ φ₂ => Selection.Or φ₁.castToAnnotatedTuple φ₂.castToAnnotatedTuple
| Selection.True      => Selection.True

/-- The truth of a selection condition on a tuple. -/
def Selection.eval {n : ℕ} (φ: Selection T n) (tuple: Tuple T n) := match φ with
| Selection.BT  φ     => φ.eval tuple
| Selection.Not φ     => ¬ (φ.eval tuple)
| Selection.And φ₁ φ₂ => (φ₁.eval tuple) ∧ (φ₂.eval tuple)
| Selection.Or  φ₁ φ₂ => (φ₁.eval tuple) ∨ (φ₂.eval tuple)
| Selection.True      => true

@[reducible] def Selection.evalDecidable {n : ℕ} (φ : Selection T n) : DecidablePred φ.eval :=
  λ t => match φ with
    | Selection.BT φ      => φ.evalDecidable t
    | Selection.Not φ     => match φ.evalDecidable t with
      | isTrue h  => isFalse (by simp [Selection.eval, h])
      | isFalse h => isTrue  (by simp [Selection.eval, h])
    | Selection.And φ₁ φ₂  => match φ₁.evalDecidable t, φ₂.evalDecidable t with
      | isTrue h₁, isTrue h₂   => isTrue  (by simp [Selection.eval, h₁, h₂])
      | isFalse h, _ | _, isFalse h => isFalse (by simp [Selection.eval, h])
    | Selection.Or φ₁ φ₂   => match φ₁.evalDecidable t, φ₂.evalDecidable t with
      | isTrue h, _ | _, isTrue h => isTrue (by simp [Selection.eval, h])
      | isFalse h₁, isFalse h₂    => isFalse (by simp [Selection.eval, h₁, h₂])
    | Selection.True       => isTrue (rfl)

end Lax392996.RelationalAlgebra
end
