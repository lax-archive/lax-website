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

/-- **projection**: `⟦Π_{t₁,…,t_n}(q)⟧_I ≝ {|(t₁(u),…,t_n(u)) | u ∈ ⟦q⟧_I|}`. -/
axiom eval_proj : ∀ {n k : ℕ} (ts : Tuple (Term T k) n) (q : Query T k) (d : Database T),
  Query.evaluate (Query.Proj ts q) d = (Query.evaluate q d).map (fun u l => (ts l).eval u)

end Lax392996.MultisetSemantics
end
