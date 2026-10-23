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
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Finite.Basic
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

-- Lax392996.SemiringsWithMonus
section
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

/-- An alternative linear order on a type, used to order annotations when
they share a column with data values. -/
class HasAltLinearOrder (α : Type u) where
  altOrder : LinearOrder α

end Lax392996.SemiringsWithMonus
end

-- Lax392996.AnnotatedDatabases
section
namespace Lax392996.AnnotatedDatabases.AnnotatedDatabase
end Lax392996.AnnotatedDatabases.AnnotatedDatabase

namespace Lax392996.AnnotatedDatabases.AnnotatedRelation
end Lax392996.AnnotatedDatabases.AnnotatedRelation

namespace Lax392996.AnnotatedDatabases.AnnotatedTuple
end Lax392996.AnnotatedDatabases.AnnotatedTuple

namespace Lax392996.AnnotatedDatabases.Tuple
end Lax392996.AnnotatedDatabases.Tuple

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

/-- `V ⊕ K` is a value type: data values are below annotations, and
annotations are compared through the alternative linear order of `K`. -/
instance instValueTypeSumOfHasAltLinearOrderOfSemiringWithMonus {V K : Type}
    [ValueType V] [HasAltLinearOrder K] [SemiringWithMonus K] : ValueType (V⊕K) where
  zero := Sum.inr 0

  add a b := match a,b with
  | Sum.inl a', Sum.inl b' => Sum.inl (a'+b')
  | Sum.inr a', Sum.inr b' => Sum.inr (a'+b')
  | Sum.inl a', Sum.inr b' => Sum.inl (a')
  | Sum.inr a', Sum.inl b' => Sum.inl (b')

  sub a b := match a,b with
  | Sum.inl a', Sum.inl b' => Sum.inl (a'-b')
  | Sum.inr a', Sum.inr b' => Sum.inr (a'-b')
  | Sum.inl a', Sum.inr b' => Sum.inl (a')
  | Sum.inr a', Sum.inl b' => Sum.inl (b')

  mul a b := match a,b with
  | Sum.inl a', Sum.inl b' => Sum.inl (a'*b')
  | Sum.inr a', Sum.inr b' => Sum.inr (a'*b')
  | Sum.inl a', Sum.inr b' => Sum.inl (a')
  | Sum.inr a', Sum.inl b' => Sum.inl (b')

  add_assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp[(· + ·)] <;> exact add_assoc _ _ _

  add_comm a b := by
    cases a <;> cases b <;> simp[(· + ·)] <;> exact add_comm _ _

  le a b := match a,b with
  | Sum.inl a', Sum.inl b' => a'≤b'
  | Sum.inr a', Sum.inr b' => HasAltLinearOrder.altOrder.le a' b'
  | Sum.inl a', Sum.inr b' => True
  | Sum.inr a', Sum.inl b' => False

  le_refl a := by
    cases a <;> simp

  le_antisymm a b := by
    cases a <;> cases b <;> simp
    . exact le_antisymm
    . exact HasAltLinearOrder.altOrder.le_antisymm _ _

  le_trans a b c := by
    cases a <;> cases b <;> cases c <;> simp
    . exact le_trans
    . exact HasAltLinearOrder.altOrder.le_trans _ _ _

  le_total a b := by
    cases a <;> cases b <;> simp
    . exact le_total _ _
    . next x y =>
      exact HasAltLinearOrder.altOrder.le_total x y

  toDecidableLE :=
    λ a b ↦ match a, b with
    | Sum.inl a', Sum.inl b' => inferInstance
    | Sum.inr a', Sum.inr b' => inferInstance
    | Sum.inl a', Sum.inr b' => isTrue (trivial)
    | Sum.inr a', Sum.inl b' => isFalse (id)

end Lax392996.AnnotatedDatabases
end
