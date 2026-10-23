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
namespace Lax392996.RelationalAlgebra.CompOp.eval
end Lax392996.RelationalAlgebra.CompOp.eval

namespace Lax392996.RelationalAlgebra

open Lax392996.Databases

universe u v

variable {T : Type} [ValueType T]

/-- Comparison operator, as used by the `HAVING` operator. -/
inductive CompOp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

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

/-- **projection**: the annotation rides along unchanged. -/
axiom aeval_proj : ∀ {n k : ℕ} (ts : Tuple (Term T k) n) (q : Query T k)
    (hq : (Query.Proj ts q).source) (d : AnnotatedDatabase T K),
  Query.evaluateAnnotated (Query.Proj ts q) hq d
    = (Query.evaluateAnnotated q (Query.source_proj hq rfl) d).map
        (fun p => ⟨fun l => (ts l).eval p.fst, p.snd⟩)

end Lax392996.AnnotatedSemantics
end
