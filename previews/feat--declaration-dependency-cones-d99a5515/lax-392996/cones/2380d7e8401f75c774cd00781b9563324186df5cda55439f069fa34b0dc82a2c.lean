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
import Mathlib.Logic.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder

-- Lax392996.Databases
section
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

/-- The lexicographic strict order on tuples. -/
instance instLTTuple : LT (Tuple T n) :=
  ⟨λ a b ↦ ∃ i : Fin n, (∀ j, j < i → a j = b j) ∧ a i < b i⟩

instance instLETuple : LE (Tuple T n) := ⟨λ a b ↦ a < b ∨ a = b⟩

instance instDecidableRelTupleLt : DecidableRel (λ (t₁ t₂: Tuple T n) => t₁ < t₂) :=
  λ f g ↦
    let _ : DecidablePred (fun i : Fin n => (∀ j, j < i → f j = g j) ∧ f i < g i) :=
      fun i => @instDecidableAnd _ _
        (@Fintype.decidableForallFintype (Fin n) (fun j => j < i → f j = g j)
          (fun _j => inferInstance) _)
        inferInstance
    if h : ∃ i : Fin n, (∀ j, j < i → f j = g j) ∧ f i < g i then
      isTrue (h)
    else
      isFalse (h)

/-- Tuples are linearly ordered, lexicographically. -/
instance instLinearOrderTuple : LinearOrder (Tuple T n) where
  le_refl := by simp[(· ≤ ·)]

  le_antisymm := by
    simp[(· ≤ ·)]
    intro a b hab hba
    cases hab with
    | inl hab' =>
      cases hba with
      | inl hba' =>
        simp only[(· < ·)] at *
        rcases hab' with ⟨iab,hiab⟩
        rcases hba' with ⟨iba,hiba⟩
        by_cases h : iab=iba
        . rw[h] at hiab
          have := lt_trans hiab.right hiba.right
          have := lt_asymm (lt_trans hiab.right hiba.right)
          contradiction
        . by_cases h' : iab<iba
          . have heq := hiba.left iab h'
            have := hiab.right
            rw[heq] at this
            have := lt_asymm this
            contradiction
          . have h'' : iba<iab := by
              refine lt_iff_le_and_ne.mpr ?_
              constructor
              . exact le_of_not_gt h'
              . exact fun a ↦ h (id (Eq.symm a))
            have heq := hiab.left iba h''
            have := hiba.right
            rw[heq] at this
            have := lt_asymm this
            contradiction
      | inr hba' => exact Eq.symm hba'
    | inr hab' => exact hab'

  le_trans := by
    intro a b c
    simp only[(· ≤ ·),(· < ·)]
    intro hab hbc
    cases hab with
    | inl habl =>
      cases hbc with
      | inl hbcl =>
        apply Or.inl
        rcases habl with ⟨iab,hiab⟩
        rcases hbcl with ⟨ibc,hibc⟩
        let i := min iab ibc
        use i
        have h : ∀ (j : Fin n), j < i → a j = c j := by
          intro j hj
          have hx := hiab.left j (lt_min_iff.mp hj).left
          have hy := hibc.left j (lt_min_iff.mp hj).right
          rw[hy] at hx; exact hx
        use h
        by_cases heq : iab = i
        . by_cases heq' : ibc = i
          . rw[heq] at hiab
            rw[heq'] at hibc
            exact lt_trans hiab.right hibc.right
          . have h' : i < ibc := lt_of_le_of_ne (min_le_right iab ibc) (ne_comm.mpr heq')
            have hab := hiab.right
            rw[heq] at hab
            have hbc := hibc.left i h'
            rw[hbc] at hab
            exact hab
        . have heq'' : ibc = i := by
            have choice : iab = i ∨ ibc = i := by
              rcases min_choice iab ibc with hc | hc
              . exact Or.inl hc.symm
              . exact Or.inr hc.symm
            tauto
          have h' : i < iab := lt_of_le_of_ne (min_le_left iab ibc) (ne_comm.mpr heq)
          have hbc := hibc.right
          rw[heq''] at hbc
          have hab := hiab.left i h'
          rw[hab]
          exact hbc
      | inr hbcr =>
        rw[← hbcr]
        exact Or.inl habl
    | inr habr =>
      rw[habr]
      exact hbc

  le_total := by
    intro a b
    simp only[(· ≤ ·)]
    by_cases heq: a=b
    . tauto
    . by_cases h: ∃ i, (∀ j < i, a j = b j) ∧ a i < b i
      . apply Or.inl; apply Or.inl
        simp only[(· < ·)]
        tauto
      . apply Or.inr; apply Or.inl
        simp only[(· < ·)]
        have hexists : ∃ k, ¬ a k = b k := by
          refine Classical.byContradiction fun hne => ?_
          simp at hne
          exact heq (funext hne)
        have hdec : DecidablePred (fun j : Fin n => ¬ a j = b j) := fun j => instDecidableNot
        obtain ⟨k, hk⟩ : ∃ k, k = Fin.find (λ j ↦ ¬ a j = b j) hexists := ⟨_, rfl⟩
        use k
        have hspec : ¬ a k = b k := by rw [hk]; exact Fin.find_spec hexists
        have hmin_ab : ∀ j < k, a j = b j := by
          intro j hj
          rw [hk] at hj
          have := Fin.find_min hexists hj
          simp at this
          exact this
        have hmin_ba : ∀ j < k, b j = a j := fun j hj => (hmin_ab j hj).symm
        refine ⟨hmin_ba, ?_⟩
        simp at h
        have hle : b k ≤ a k := h k hmin_ab
        exact lt_iff_le_and_ne.mpr ⟨hle, fun h => hspec h.symm⟩

  lt_iff_le_not_ge := by
    intro a b
    simp only[(· ≤ ·)]
    apply Iff.intro
    . intro hab
      constructor
      . tauto
      . simp only[(· < ·)] at *
        rcases hab with ⟨i, hi⟩
        simp
        constructor
        . intro k h
          cases hki : compare k i with
          | eq =>
            simp at hki
            rw[hki]
            exact le_of_lt hi.right
          | lt =>
            simp[compare] at hki
            have := hi.left k hki
            simp[this]
          | gt =>
            simp only[compare,compareOfLessAndEq] at hki
            by_cases hki' : k < i
            . simp[hki'] at hki
            . by_cases hki'' : k = i
              . rw[hki''] at hki
                simp at hki
              . simp[hki'] at hki
                have hgt : k>i := by
                  have hle := le_of_not_gt hki'
                  apply lt_of_le_of_ne
                  . exact hle
                  . exact fun a ↦ hki'' (id (Eq.symm a))
                have h' := h i hgt
                rw[h'] at hi
                have hc : a i < a i := hi.right
                simp at hc
        . intro heq
          rw[heq] at hi
          simp at hi
    . intro ⟨h₁,h₂⟩
      simp at h₂
      have hne : a ≠ b := by
        rw[ne_comm]; exact h₂.right
      simp[hne] at h₁
      exact h₁

  toDecidableLE :=
    λ a b ↦
      match (inferInstance : Decidable (a<b)), (inferInstance : Decidable (a=b)) with
      | isTrue h₁, _           => isTrue (Or.inl h₁)
      | _, isTrue h₂           => isTrue (Or.inr h₂)
      | isFalse h₁, isFalse h₂ => isFalse (
        fun h ↦
          match h with
            | Or.inl h' => h₁ h'
            | Or.inr h' => h₂ h'
        )

/-- A relation of arity `arity` over `T`: a finite multiset of tuples. -/
def Relation (T) (arity: ℕ) := Multiset (Tuple T arity)

/-- Transport of a relation along an equality of arities. -/
def Relation.cast (heq: n=m) (r: Relation T n): Relation T m :=
  Eq.ndrec (motive := fun m => Relation T m) r heq

instance instAddRelation {arity : ℕ} : Add (Relation T arity) := by
  show Add (Multiset (Tuple T arity))
  infer_instance

/-- The cross product of two relations, concatenating the tuples. -/
instance instHMulRelationHAddNat {a₁ a₂ : ℕ} :
    HMul (Relation T a₁) (Relation T a₂) (Relation T (a₁+a₂)) where
  hMul r s :=
    Multiset.map (λ ((x,y) : (Tuple T a₁)×(Tuple T a₂)) ↦
      Fin.append x y
    ) (Multiset.product r s)

/-- A database: a list of named relations, each with its arity. -/
def Database (T) := List (String × Σ n, Relation T n)

/-- The relation named `s` of arity `n` in a database, if any. -/
def Database.find (n: ℕ) (s: String) (d: Database T) : Option (Relation T n) :=
  let rec f
  | [] => none
  | (s',rn)::tl => if h: n = rn.fst ∧ s=s' then some (Eq.mp (by rw[h.left]) rn.snd) else f tl
  f d

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
namespace Lax392996.AnnotatedDatabases.Tuple
end Lax392996.AnnotatedDatabases.Tuple

namespace Lax392996.AnnotatedDatabases.instValueTypeSumOfHasAltLinearOrderOfSemiringWithMonus
end Lax392996.AnnotatedDatabases.instValueTypeSumOfHasAltLinearOrderOfSemiringWithMonus

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

instance instAddAnnotatedRelation {arity : ℕ} : Add (AnnotatedRelation T K arity) := by
  show Add (Multiset (AnnotatedTuple T K arity))
  infer_instance

/-- A `K`-instance: a list of named annotated relations, each with its arity. -/
def AnnotatedDatabase (T : Type) (K : Type u) := List (String × Σ n, AnnotatedRelation T K n)

/-- The annotated relation named `s` of arity `n` in a `K`-instance, if any. -/
def AnnotatedDatabase.find (n: ℕ) (s: String) (d: AnnotatedDatabase T K) :
    Option (AnnotatedRelation T K n) :=
  let rec f
  | [] => none
  | (s',rn)::tl => if h: n = rn.fst ∧ s =s' then some (Eq.mp (by rw[h.left]) rn.snd) else f tl
  f d

end Lax392996.AnnotatedDatabases
end

-- Lax392996.RelationalAlgebra
section
namespace Lax392996.RelationalAlgebra

open Lax392996.Databases

universe u v

variable {T : Type} [ValueType T]

/-- Comparison operator, as used by the `HAVING` operator. -/
inductive CompOp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- Semantics of a comparison operator over any linearly ordered value
domain. -/
def CompOp.eval {V : Type u} [LinearOrder V] : CompOp → V → V → Prop
  | .eq, a, b => a = b
  | .ne, a, b => a ≠ b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

instance instDecidableEval {V : Type u} [LinearOrder V] (op : CompOp) (a b : V) :
    Decidable (op.eval a b) := by
  cases op <;> simp only [CompOp.eval] <;> infer_instance

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

/-- An aggregate function on sequences of values, the aggregate interface
of the fused `HAVING` operator. -/
def SeqAggFunc (T : Type) := List T → T

/-- The queries, indexed by arity: the operators of the paper's grammar,
the provenance aggregation `ProvSum` that the rewriting emits, and the
fused `HAVING` operator. -/
inductive Query (T: Type) : ℕ → Type
| Rel   : (n: ℕ) → String → Query T n
| Proj  {n m : ℕ} : Tuple (Term T n) m → Query T n → Query T m
| Sel   {n : ℕ} : Selection T n → Query T n → Query T n
| Prod {n₁ n₂ n : ℕ} {hn: n₁+n₂=n} : Query T n₁ → Query T n₂ → Query T n
| Sum   {n : ℕ} : Query T n → Query T n → Query T n
| Dedup {n : ℕ} : Query T n → Query T n
| Diff  {n : ℕ} : Query T n → Query T n → Query T n
/-- Provenance aggregation: group by the key columns of the first
argument and `⊕`-sum the term of the second over each group into a single
trailing output column. It is the target of the rewriting of duplicate
elimination and of difference. -/
| ProvSum {m n₁ : ℕ} : Tuple (Fin m) n₁ → Term T m → Query T m → Query T (n₁+1)
/-- The fused `HAVING` operator: grouping by the indices of the first
argument, computing the sequence aggregates of the third argument applied
to the terms of the second, each group read in the canonical tuple order,
and keeping only the groups whose aggregate value in column `l` compares,
through the comparison operator, with the value of the term on the group
key. The output has the group key followed by the aggregate values. -/
| Having {m n₁ n₂ : ℕ} : Tuple (Fin m) n₁ → Tuple (Term T m) n₂ → Tuple (SeqAggFunc T) n₂ →
    CompOp → Fin n₂ → Term T n₁ → Query T m → Query T (n₁+n₂)

/-- The source fragment: the queries written with the operators of the
paper's grammar only, without `ProvSum` and `Having`. -/
def Query.source {n : ℕ} (q: Query T n): Prop := match q with
| Query.Rel   n  s  => True
| Query.Proj  _ q   => q.source
| Query.Sel   _  q  => q.source
| Query.Prod  q₁ q₂ => q₁.source ∧ q₂.source
| Query.Sum   q₁ q₂ => q₁.source ∧ q₂.source
| Query.Dedup q     => q.source
| Query.Diff  q₁ q₂ => q₁.source ∧ q₂.source
| Query.ProvSum _ _ q => False
| Query.Having _ _ _ _ _ _ _ => False

/-- The arguments of a source cross product are source queries. A proof
carried as a definition, since the concept dialect has no theorem command;
the recursive definitions over source queries use it. -/
def Query.source_prod {n n₂ : ℕ} {q: Query T n} :
  q.source → ∀ {n₁} {q₁: Query T n₁} {q₂: Query T n₂} {hn: n₁+n₂=n}
    (_: q = @Query.Prod T n₁ n₂ n hn q₁ q₂), q₁.source ∧ q₂.source := by
    intro hna n₁ q₁ q₂ hn₁ hq
    unfold Query.source at hna
    simp[hq] at hna
    assumption

/-- The arguments of a source multiset sum are source queries. -/
def Query.source_sum {n : ℕ} {q: Query T n} :
  q.source → ∀ {q₁: Query T n} {q₂: Query T n} (_: q = Query.Sum q₁ q₂), q₁.source ∧ q₂.source := by
    intro hna q₁ q₂ hq
    unfold Query.source at hna
    simp[hq] at hna
    assumption

/-- The arguments of a source difference are source queries. -/
def Query.source_diff {n : ℕ} {q: Query T n} :
  q.source → ∀ {q₁: Query T n} {q₂: Query T n} (_: q = Query.Diff q₁ q₂), q₁.source ∧ q₂.source := by
    intro hna q₁ q₂ hq
    unfold Query.source at hna
    simp[hq] at hna
    assumption

/-- The argument of a source projection is a source query. -/
def Query.source_proj {n : ℕ} {q: Query T n} :
  q.source → ∀ {m} {t} {q': Query T m} (_: q = Query.Proj t q'), q'.source := by
    intro hna m t q' hq
    unfold Query.source at hna
    rw[hq] at hna
    assumption

/-- The argument of a source selection is a source query. -/
def Query.source_sel {n : ℕ} {q: Query T n} :
  q.source → ∀ {φ} {q': Query T n} (_: q = Query.Sel φ q'), q'.source := by
    intro hna φ q' hq
    unfold Query.source at hna
    rw[hq] at hna
    assumption

/-- The argument of a source duplicate elimination is a source query. -/
def Query.source_dedup {n : ℕ} {q: Query T n} :
  q.source → ∀ {q': Query T n} (_: q = Query.Dedup q'), q'.source := by
    intro hna q' hq
    unfold Query.source at hna
    rw[hq] at hna
    assumption

/-- The measure the recursive semantics is defined along: the depth of the
query, aggregation operators counting for three. -/
def Query.aggdepth2_plus_depth {n : ℕ} (q: Query T n) : ℕ := match q with
| Query.Rel   n  s  => 0
| Query.Proj  _ q   => let d := q.aggdepth2_plus_depth; d+1
| Query.Sel   _  q  => let d := q.aggdepth2_plus_depth; d+1
| Query.Prod  q₁ q₂ =>
  let d₁ := q₁.aggdepth2_plus_depth
  let d₂ := q₂.aggdepth2_plus_depth
  (max d₁ d₂)+1
| Query.Sum   q₁ q₂ =>
  let d₁ := q₁.aggdepth2_plus_depth
  let d₂ := q₂.aggdepth2_plus_depth
  (max d₁ d₂)+1
| Query.Dedup q     => let d := q.aggdepth2_plus_depth; d+1
| Query.Diff  q₁ q₂ =>
  let d₁ := q₁.aggdepth2_plus_depth
  let d₂ := q₂.aggdepth2_plus_depth
  (max d₁ d₂)+1
| Query.ProvSum _ _ q => let d := q.aggdepth2_plus_depth; (d+3)
| Query.Having _ _ _ _ _ _ q => let d := q.aggdepth2_plus_depth; (d+3)

end Lax392996.RelationalAlgebra
end

-- Lax392996.AnnotatedSemantics
section
namespace Lax392996.AnnotatedSemantics

open Lax392996.SemiringsWithMonus Lax392996.Databases Lax392996.AnnotatedDatabases

open Lax392996.RelationalAlgebra

variable {T : Type} [ValueType T]

variable {K : Type} [SemiringWithMonus K]

@[reducible] def Selection.evalDecidableAnnotated {n : ℕ} (φ : Selection T n) :
  DecidablePred (λ (ta: AnnotatedTuple T K n) ↦ φ.eval ta.fst) :=
    λ t => match φ.evalDecidable t.fst with
      | isTrue h  => isTrue (by simp [h])
      | isFalse h => isFalse  (by simp [h])

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

/-- Annotated (m-semiring) semantics of a source query.

The `Diff` case follows ProvSQL: every tuple slot `(u, α)` of `r₁` is kept,
with its annotation rewritten to `α ⊖ Σ β` where `Σ β` is the semiring sum of
the annotations of all copies of `u` in `r₂`. Duplicate elimination keeps
each data part once, annotated by the `⊕`-sum of the annotations of its
copies. -/
def Query.evaluateAnnotated {n : ℕ} (q: Query T n) (hq: q.source) (d: AnnotatedDatabase T K) :
    AnnotatedRelation T K n := match q with
| Query.Rel   n  s  =>
  match h : d.find n s with
  | none => (∅: Multiset (AnnotatedTuple T K n))
  | some rn => rn
| @Query.Proj _ n m ts q' =>
  let r := evaluateAnnotated q' (Query.source_proj hq rfl) d
  r.map (λ t ↦ ⟨λ k ↦ (ts k).eval t.fst, t.snd⟩)
| Query.Sel   φ  q  =>
  let r := evaluateAnnotated q (Query.source_sel hq rfl) d
  @Multiset.filter _ (λ ta ↦ φ.eval ta.fst) (Selection.evalDecidableAnnotated φ) r
| @Query.Prod _ n₁ n₂ n hn q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ (Query.source_prod hq rfl).left d
  let r₂ := evaluateAnnotated q₂ (Query.source_prod hq rfl).right d
  Multiset.map (λ (x,y) ↦ ⟨
    Eq.mp (by simp[hn]; rfl)
    (Fin.append x.fst y.fst),
    x.snd*y.snd
  ⟩) (Multiset.product r₁ r₂)
| Query.Sum   q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ (Query.source_sum hq rfl).left d
  let r₂ := evaluateAnnotated q₂ (Query.source_sum hq rfl).right d
  r₁+r₂
| Query.Dedup q     =>
  let r := evaluateAnnotated q (Query.source_dedup hq rfl) d
  groupByKey r
| Query.Diff  q₁ q₂ =>
  let r₁ := evaluateAnnotated q₁ (Query.source_diff hq rfl).left d
  let r₂ := evaluateAnnotated q₂ (Query.source_diff hq rfl).right d
  r₁.map
    λ (u,α) ↦ ⟨u, α - annotationSum r₂ u⟩
| Query.ProvSum _ _ _ => False.elim (by
  simp[Query.source] at hq
)

end Lax392996.AnnotatedSemantics
end

-- Lax392996.BooleanFunctions
section
namespace Lax392996.BooleanFunctions

open Lax392996.SemiringsWithMonus

variable {X : Type}

/-- The type of Boolean functions over Boolean assignments to `X`:
`(X → Bool) → Bool` with pointwise operations. -/
def BoolFunc (X : Type) := (X → Bool) → Bool

instance instZeroBoolFunc : Zero (BoolFunc X) := ⟨λ _ ↦ False⟩

instance instAddBoolFunc : Add  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) || (f₂ ν)⟩

instance instOneBoolFunc : One  (BoolFunc X) := ⟨λ _ ↦ True⟩

instance instMulBoolFunc : Mul  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) && (f₂ ν)⟩

instance instLEBoolFunc : LE   (BoolFunc X) := ⟨λ f₁ f₂ ↦ ∀ ν : X → Bool, (f₁ ν) ≤ (f₂ ν)⟩

instance instSubBoolFunc : Sub  (BoolFunc X) := ⟨λ f₁ f₂ ν ↦ (f₁ ν) && !(f₂ ν)⟩

instance instCommSemiringBoolFunc : CommSemiring (BoolFunc X) where
  add_assoc := by
    intro a b c
    simp[(· + ·),Add.add]
    apply funext
    intro x
    exact Bool.or_assoc _ _ _

  add_comm := by
    intro a b
    simp[(· + ·),Add.add]
    apply funext
    intro x
    exact Bool.or_comm _ _

  zero_add := by tauto

  add_zero := by
    simp[(· + ·),Add.add]
    intro a
    apply funext
    simp
    tauto

  nsmul := nsmulRec

  left_distrib := by
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    intro a b c
    apply funext
    intro x
    exact Bool.and_or_distrib_left _ _ _

  right_distrib := by
    simp[(· + ·),Add.add,(· * ·),Mul.mul]
    intro a b c
    apply funext
    intro x
    exact Bool.and_or_distrib_right _ _ _

  zero_mul := by tauto

  mul_zero := by
    simp[(· * ·),Mul.mul]
    intro a
    apply funext
    simp
    tauto

  mul_assoc := by
    intro a b c
    simp[(· * ·),Mul.mul]
    apply funext
    intro x
    exact Bool.and_assoc _ _ _

  mul_comm := by
    intro a b
    simp[(· * ·),Mul.mul]
    apply funext
    intro x
    exact Bool.and_comm _ _

  one_mul := by tauto

  mul_one := by
    simp[(· * ·),Mul.mul]
    intro a
    apply funext
    simp
    tauto

/-- `BoolFunc X` is a commutative m-semiring with pointwise `||` as addition,
pointwise `&&` as multiplication, and pointwise implication as natural order. -/
instance instSemiringWithMonusBoolFunc : SemiringWithMonus (BoolFunc X) where
  le_refl := by tauto

  le_trans := by tauto

  le_antisymm := by
    simp[(· ≤ ·)]
    intro a b hab hba
    apply funext
    intro ν
    exact Bool.le_antisymm (hab ν) (hba ν)

  le_self_add := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  le_add_self := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  add_le_add_left := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    tauto

  exists_add_of_le := by
    simp[(· + ·),Add.add,(· ≤ ·)]
    intro a b h
    use b
    apply funext
    intro x
    cases ha : a x
    . tauto
    . apply (h x) ha

  monus_spec := by
    intro a b c
    simp[(· + ·),Add.add,(· ≤ ·),(· - ·),Sub.sub]
    apply Iff.intro
    . intro h ν ha
      cases hb : b ν <;> simp
      . exact h ν ha hb
    . intro h ν ha hb
      have h' : b ν = true ∨ c ν = true := h ν ha
      simp[hb] at h'
      exact h'

  delta := id
  delta_zero := rfl
  delta_natCast_pos := by
    have hidem : ∀ a : BoolFunc X, a + a = a := fun a => funext fun ν => by
      show (a ν || a ν) = a ν
      simp
    have hcast : ∀ {n : ℕ}, 0 < n → (n : BoolFunc X) = 1 := by
      intro n hn
      induction n with
      | zero => omega
      | succ m ih =>
        rcases Nat.eq_zero_or_pos m with hm | hm
        · rw [hm]; simp
        · rw [Nat.cast_succ, ih hm, hidem 1]
    intro n hn
    exact hcast hn
  delta_absorb := fun a b => funext fun ν => by
    show (a ν && (a ν || b ν)) = a ν
    cases a ν <;> cases b ν <;> rfl

end Lax392996.BooleanFunctions
end

-- Lax392996.MultisetSemantics
section
namespace Lax392996.MultisetSemantics

open Lax392996.Databases Lax392996.RelationalAlgebra

variable {T : Type} [ValueType T]

/-- Addition as a binary function, the fold of the `⊕`-sum performed by
the provenance aggregation `Query.ProvSum`. -/
def addFn (a b : T) := a + b

instance instCommutativeAddFn : @Std.Commutative T addFn where
  comm := add_comm

instance instAssociativeAddFn : @Std.Associative T addFn where
  assoc := add_assoc

/-- The occurrences of the group of key `g` in relation `r`: the multiset of
matching tuples, as a list sorted by the canonical linear order on tuples.
The sort order plays the role of the ordering along which
non-commutative sequence aggregates read the occurrences of a group; for
commutative aggregates it is irrelevant. -/
def Relation.groupSeq {m n₁ : ℕ} (is : Tuple (Fin m) n₁) (r : Relation T m) (g : Tuple T n₁) :
    List (Tuple T m) :=
  Multiset.sort
    (@Multiset.filter _ (fun u => ∀ k' : Fin n₁, u (is k') = g k')
      (fun u => @Nat.decidableForallFin n₁ (fun k' => u (is k') = g k') (fun _ => inferInstance)) r)
    (· ≤ ·)

/-- Multiset semantics of a query over a plain database.

The `Diff` case is all-or-nothing difference: every copy of a tuple that
occurs at all in `r₂` is removed from `r₁`, which is what the monus-based
annotated semantics of difference gives on `0`/`1`-annotated inputs. -/
def Query.evaluate {n : ℕ} (q: Query T n) (d: Database T): Relation T n := match q with
| Query.Rel   n  s  =>
  match d.find n s with
  | none => (∅: Multiset (Tuple T n))
  | some rn => rn
| Query.Proj ts q => let r := evaluate q d; Multiset.map (λ t ↦ λ k ↦ (ts k).eval t) r
| Query.Sel   φ  q  => let r := evaluate q d; @Multiset.filter _ φ.eval φ.evalDecidable r
| @Query.Prod _ n₁ n₂ n hn q₁ q₂ =>
  let r₁ := evaluate q₁ d
  let r₂ := evaluate q₂ d
  (r₁ * r₂).cast hn
| Query.Sum   q₁ q₂ => let r₁ := evaluate q₁ d; let r₂ := evaluate q₂ d; r₁ + r₂
| Query.Dedup q     => let r := evaluate q d; Multiset.dedup r
| Query.Diff  q₁ q₂ =>
  let r₁ := evaluate q₁ d
  let r₂ : Multiset (Tuple T _) := evaluate q₂ d
  r₁.filter (fun t ↦ t ∉ r₂)
| @Query.ProvSum _ m n₁ is t q =>
    let r := evaluate (Query.Dedup (Query.Proj (λ (k: Fin n₁) ↦ Term.index (is k)) q)) d
    let s := evaluate q d
    r.map (λ g ↦ Fin.append g (
      λ _: Fin 1 ↦ (
        (@Multiset.filter _ (λ u ↦ ∀ k': Fin n₁, u (is k') = g k')
          (fun u => @Nat.decidableForallFin n₁ (fun k' => u (is k') = g k') (fun _ => inferInstance))
          s).map (λ u ↦ t.eval u)
      ).fold addFn 0
    ))
| @Query.Having _ m n₁ n₂ is ts fs op l s q =>
    let keys := evaluate (Query.Dedup (Query.Proj (λ (k: Fin n₁) ↦ Term.index (is k)) q)) d
    let r := evaluate q d
    Multiset.map
      (λ g ↦ Fin.append g
        (λ (k: Fin n₂) ↦ (fs k) ((Relation.groupSeq is r g).map (ts k).eval)))
      (@Multiset.filter _
        (λ g ↦ op.eval ((fs l) ((Relation.groupSeq is r g).map (ts l).eval)) (s.eval g))
        (fun g => instDecidableEval op _ _)
        keys)
termination_by q.aggdepth2_plus_depth
decreasing_by
  all_goals simp[Query.aggdepth2_plus_depth]
  any_goals refine Nat.lt_add_one_of_le ?_
  any_goals exact Nat.le_max_left _ _
  any_goals exact Nat.le_max_right _ _

end Lax392996.MultisetSemantics
end

-- Lax392996.ProbabilisticDatabases
section
namespace Lax392996.ProbabilisticDatabases

open Lax392996.SemiringsWithMonus Lax392996.BooleanFunctions Lax392996.Databases

open Lax392996.AnnotatedDatabases Lax392996.RelationalAlgebra Lax392996.MultisetSemantics

variable {X : Type} [Fintype X] [DecidableEq X]

/-- A probability assignment to a finite set `X` of Boolean variables: each
variable is assigned a rational probability in `[0, 1]`. -/
structure ProbAssignment (X : Type) where
  /-- The probability assigned to each variable. -/
  prob : X → ℚ
  /-- Probabilities are non-negative. -/
  prob_nonneg : ∀ x, 0 ≤ prob x
  /-- Probabilities are at most `1`. -/
  prob_le_one : ∀ x, prob x ≤ 1

namespace ProbAssignment

variable (P : ProbAssignment X)

/-- Probability of a single valuation `v : X → Bool`, under the independence
assumption: `Pr(v) = ∏_{v(x)=⊤} Pr(x) · ∏_{v(x)=⊥} (1 - Pr(x))`. -/
def valProb (v : X → Bool) : ℚ :=
  ∏ x, if v x then P.prob x else 1 - P.prob x

/-- Probability of a Boolean function: `Pr(f) = ∑_{v ⊨ f} Pr(v)`. -/
def funcProb (f : BoolFunc X) : ℚ :=
  ∑ v : X → Bool, if f v then P.valProb v else 0

end ProbAssignment

/-- Membership of a tuple in a relation, that of multisets. -/
instance instMembershipRelation {T : Type} {n : ℕ} :
    Membership (Tuple T n) (Relation T n) := by
  show Membership (Tuple T n) (Multiset (Tuple T n))
  infer_instance

/-- Decidability of membership of a tuple in a relation. -/
instance instDecidableMemRelation {T : Type} [ValueType T] {n : ℕ}
    (t : Tuple T n) (r : Relation T n) : Decidable (t ∈ r) :=
  Multiset.decidableMem t r

variable {T : Type} [ValueType T]

/-- The disjunctive tuple annotation `tupleAnnotation r t = ⋁_{(t,α) ∈ r} α`:
the OR over the annotations of all annotated tuples in `r` whose data part
equals `t`. -/
def tupleAnnotation {n : ℕ} (r : AnnotatedRelation T (BoolFunc X) n) (t : Tuple T n) :
    BoolFunc X :=
  (Multiset.map Prod.snd
    (@Multiset.filter _ (fun p : AnnotatedTuple T (BoolFunc X) n => p.fst = t)
      (fun p => instDecidableEqTuple p.fst t) r)).sum

/-- The random world of a `BoolFunc X`-annotated relation under a valuation
`v`: the plain relation consisting of the data parts of the annotated tuples
whose annotation evaluates to `true` at `v`. -/
def randomWorld {n : ℕ} (v : X → Bool) (r : AnnotatedRelation T (BoolFunc X) n) :
    Multiset (Tuple T n) :=
  Multiset.map Prod.fst
    (@Multiset.filter _ (fun p : AnnotatedTuple T (BoolFunc X) n => p.snd v = true)
      (fun p => instDecidableEqBool (p.snd v) true) r)

/-- The random world of a `BoolFunc X`-annotated database: each annotated
relation is replaced by its random world. -/
def AnnotatedDatabase.randomWorld
    (v : X → Bool) (Î : AnnotatedDatabase T (BoolFunc X)) : Database T :=
  Î.map (fun e => (e.fst, ⟨e.snd.fst, Lax392996.ProbabilisticDatabases.randomWorld v e.snd.snd⟩))

namespace ProbAssignment

variable (P : ProbAssignment X)

/-- Marginal probability that the tuple `t` appears in the output of `q`
when evaluated on a random world of `Î`. -/
noncomputable def marginalProb {n : ℕ}
    (q : Query T n) (Î : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n) : ℚ :=
  ∑ v : X → Bool,
    if t ∈ Query.evaluate q (AnnotatedDatabase.randomWorld v Î) then P.valProb v else 0

end ProbAssignment

end Lax392996.ProbabilisticDatabases
end

-- Lax392996.ProbabilisticEvaluation
section
namespace Lax392996.ProbabilisticEvaluation

open Lax392996.SemiringsWithMonus Lax392996.BooleanFunctions Lax392996.Databases

open Lax392996.AnnotatedDatabases Lax392996.RelationalAlgebra Lax392996.MultisetSemantics

open Lax392996.AnnotatedSemantics Lax392996.ProbabilisticDatabases

/-- **Theorem 12.** The marginal probability of a tuple is the probability
of its disjunctive annotation in the annotated answer. -/
axiom theorem_12 : ∀ {X : Type} [Fintype X] [DecidableEq X] {T : Type} [ValueType T]
    (P : ProbAssignment X) {n : ℕ} (q : Query T n) (hq : q.source)
    (Î : AnnotatedDatabase T (BoolFunc X)) (t : Tuple T n),
  ProbAssignment.marginalProb P q Î t
    = ProbAssignment.funcProb P (tupleAnnotation (Query.evaluateAnnotated q hq Î) t)

end Lax392996.ProbabilisticEvaluation
end
