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
namespace Lax392996.RelationalAlgebra.CompOp.eval
end Lax392996.RelationalAlgebra.CompOp.eval

namespace Lax392996.RelationalAlgebra.Selection.evalDecidable
end Lax392996.RelationalAlgebra.Selection.evalDecidable

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

/-- The arity of a query. -/
def Query.arity {n : ℕ} (_: Query T n) := n

end Lax392996.RelationalAlgebra
end

-- Lax392996.RewritingRules
section
namespace Lax392996.RewritingRules

open Lax392996.Databases Lax392996.RelationalAlgebra

variable {T : Type}

/-- The rewriting of a source query, rules (R1) to (R4) applied bottom up. -/
def Query.rewriting {n : ℕ} {K : Type} [ValueType T] (q: Query T n) (hq: q.source) :
    Query (T⊕K) (n+1) := match q with
| Query.Rel   n  s  => Query.Rel (n+1) s
| Query.Proj  ts q  =>
  let ts :=
    (λ (k: Fin (n+1)) => if h : ↑k<n then (ts ⟨k,h⟩).castToAnnotatedTuple
                         else Term.index (Fin.last q.arity))
  Query.Proj ts (rewriting q (Query.source_proj hq rfl))
| Query.Sel   φ  q  => Query.Sel φ.castToAnnotatedTuple (rewriting q (Query.source_sel hq rfl))
| @Query.Prod T n₁ n₂ n hn q₁ q₂ =>
  let tmp :=
    @Query.Prod (T⊕K) (n₁+1) (n₂+1) (n+2) (by omega) (rewriting q₁ (Query.source_prod hq rfl).left)
  let product := tmp (rewriting q₂ (Query.source_prod hq rfl).right)
  let ts : Tuple (Term (T⊕K) (n+2)) (n+1) :=
    (λ k: Fin (n+1) =>
      if ↑k<n₁ then Term.index (k.castLE (by simp))
    else if (↑k<n: Prop) then Term.index (Fin.ofNat _ (↑k+1))
    else Term.mul (Term.index (Fin.ofNat _ n₁)) (Term.index (Fin.ofNat _ (n+1))))
  Query.Proj ts product
| Query.Sum   q₁ q₂ =>
  Query.Sum (rewriting q₁ (Query.source_sum hq rfl).left) (rewriting q₂ (Query.source_sum hq rfl).right)
| Query.Dedup q     =>
  let q' := rewriting q (Query.source_dedup hq rfl)
  Query.ProvSum (λ (k: Fin n) ↦ k.castLE (by simp)) (Term.index (Fin.last n)) q'
| Query.Diff  q₁ q₂ =>
  let q'₁ := rewriting q₁ (Query.source_diff hq rfl).left
  let q'₂ := rewriting q₂ (Query.source_diff hq rfl).right
  let joinCond₁ :=
    ((List.range n).map
      (λ k ↦ @Selection.BT (T⊕K) (2*n+1)
        (BoolTerm.EQ (Term.index (Fin.ofNat _ k)) (Term.index (Fin.ofNat _ (k+n+1)))))).foldr
      (λ t t' ↦ Selection.And t t') Selection.True
  let prod₁t := λ r ↦ Query.Sel joinCond₁ (@Query.Prod _ (n+1) n (2*n+1) (by omega) q'₁ r)
  let prod₁r := Query.Dedup (Query.Diff
    (Query.Proj (λ (k: Fin n) ↦ (Term.index (k.castLE (Nat.le_succ _)))) q'₁)
    (Query.Proj (λ (k: Fin n) ↦ (Term.index (k.castLE (Nat.le_succ _)))) q'₂))
  let prod₁ := prod₁t (prod₁r)
  let joinCond₂ :=
    ((List.range n).map
      (λ k ↦ @Selection.BT (T⊕K) (2*n+2)
        (BoolTerm.EQ (Term.index (Fin.ofNat _ k)) (Term.index (Fin.ofNat _ (k+n+1)))))).foldr
      (λ t t' ↦ Selection.And t t') Selection.True
  have h₂ : (2*n+2 - (n+1): ℕ) = n+1  := by omega
  let prod₂t := λ r ↦ Query.Sel joinCond₂ (@Query.Prod _ (n+1) (n+1) (2*n+2) (by omega) q'₁ r)
  let prod₂r := Query.ProvSum (λ (k: Fin n) ↦ (k.castLE (by simp))) (Term.index (Fin.last n)) q'₂
  let prod₂ := prod₂t (prod₂r)
  let ts₁ := (λ (k: Fin (n+1)) ↦ Term.index (k.castLE (by omega)))
  let ts₂ := (λ (k: Fin (n+1)) ↦ if ↑k<n then Term.index (k.castLE (by omega))
                                 else Term.sub (Term.index (Fin.ofNat _ n)) (Term.index (Fin.last (2*n+1))))
  Query.Sum (Query.Proj ts₁ prod₁) (Query.Proj ts₂ prod₂)
| Query.ProvSum _ _ _ => by simp[Query.source] at hq
| Query.Having _ _ _ _ _ _ _ => by simp[Query.source] at hq

/-- **(R3) duplicate elimination.** `ε(q)` is rewritten to
`γ_{1,…,k}[#(k+1) : ⊕](q̂)`: group by the data columns and `⊕`-sum the
annotation column. -/
axiom rule_dupelim : ∀ [ValueType T] {K : Type} {n : ℕ} (q : Query T n) (hq : (Query.Dedup q).source),
  Query.rewriting (K := K) (Query.Dedup q) hq
    = Query.ProvSum (fun l : Fin n => l.castLE (by simp)) (Term.index (Fin.last n))
        (Query.rewriting q (Query.source_dedup hq rfl))

end Lax392996.RewritingRules
end
