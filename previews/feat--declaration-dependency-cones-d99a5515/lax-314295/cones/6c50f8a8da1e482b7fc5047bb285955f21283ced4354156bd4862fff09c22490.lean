-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic

-- Lax314295.KTypes
section
namespace Lax314295.KTypes

/-- The type of `k`-types over the alphabet `A`. -/
def TpType (A : Type) : ℕ → Type
  | 0 => Unit
  | k + 1 => Set (TpType A k × A × TpType A k)

/-- The `k`-type of a string: trivial for `k = 0`, and for `k + 1` the set of
triples `(tp k w₁, a, tp k w₂)` over the factorisations `w = w₁ a w₂`. -/
def tp {A : Type} : (k : ℕ) → List A → TpType A k
  | 0, _ => ()
  | k + 1, w =>
      {t : TpType A k × A × TpType A k |
        ∃ (w₁ : List A) (a : A) (w₂ : List A), w = w₁ ++ a :: w₂ ∧ t = (tp k w₁, a, tp k w₂)}

end Lax314295.KTypes
end

-- Lax314295.MSOLogic
section
namespace Lax314295.MSOLogic

/-- Formulas of monadic second-order logic over strings with letters in `A`;
first-order and second-order variables are named by natural numbers. -/
inductive MSO (A : Type) : Type
  /-- The order test `x_i ≤ x_j`. -/
  | le : ℕ → ℕ → MSO A
  /-- The label test `a (x_i)`. -/
  | lab : A → ℕ → MSO A
  /-- The membership test `x_i ∈ X_j`. -/
  | mem : ℕ → ℕ → MSO A
  /-- Negation. -/
  | not : MSO A → MSO A
  /-- Conjunction. -/
  | and : MSO A → MSO A → MSO A
  /-- Disjunction. -/
  | or : MSO A → MSO A → MSO A
  /-- First-order existential quantification `∃ x_i`. -/
  | exFO : ℕ → MSO A → MSO A
  /-- Second-order existential quantification `∃ X_i`. -/
  | exSO : ℕ → MSO A → MSO A

namespace MSO

variable {A : Type}

/-- Satisfaction of a formula in a string under a valuation of the first-order
variables by positions and of the second-order variables by sets of positions. -/
def Sat (w : List A) : (ℕ → ℕ) → (ℕ → Set ℕ) → MSO A → Prop
  | fo, _, le i j => fo i ≤ fo j
  | fo, _, lab a i => w[fo i]? = some a
  | fo, so, mem i j => fo i ∈ so j
  | fo, so, not φ => ¬ Sat w fo so φ
  | fo, so, and φ ψ => Sat w fo so φ ∧ Sat w fo so ψ
  | fo, so, or φ ψ => Sat w fo so φ ∨ Sat w fo so ψ
  | fo, so, exFO i φ => ∃ p < w.length, Sat w (Function.update fo i p) so φ
  | fo, so, exSO i φ => ∃ S ⊆ {p | p < w.length}, Sat w fo (Function.update so i S) φ

/-- A formula is first-order if it uses neither set quantification nor membership.
-/
def IsFO : MSO A → Prop
  | le _ _ => True
  | lab _ _ => True
  | mem _ _ => False
  | not φ => IsFO φ
  | and φ ψ => IsFO φ ∧ IsFO ψ
  | or φ ψ => IsFO φ ∧ IsFO ψ
  | exFO _ φ => IsFO φ
  | exSO _ _ => False

/-- The quantifier rank: the maximal number of nested quantifiers. -/
def qrank : MSO A → ℕ
  | le _ _ => 0
  | lab _ _ => 0
  | mem _ _ => 0
  | not φ => qrank φ
  | and φ ψ => max (qrank φ) (qrank ψ)
  | or φ ψ => max (qrank φ) (qrank ψ)
  | exFO _ φ => qrank φ + 1
  | exSO _ φ => qrank φ + 1

/-- The free first-order variables of a formula. -/
def freeFO : MSO A → Set ℕ
  | le i j => {i, j}
  | lab _ i => {i}
  | mem i _ => {i}
  | not φ => freeFO φ
  | and φ ψ => freeFO φ ∪ freeFO ψ
  | or φ ψ => freeFO φ ∪ freeFO ψ
  | exFO i φ => freeFO φ \ {i}
  | exSO _ φ => freeFO φ

end MSO

end Lax314295.MSOLogic
end

-- Lax314295.KTypesFOEquivalence
section
namespace Lax314295.KTypesFOEquivalence

open Lax314295.MSOLogic Lax314295.KTypes

/-- Two strings have the same `k`-type if and only if they satisfy the same
first-order sentences of quantifier rank at most `k`. -/
axiom tp_eq_iff_fo_equiv {A : Type} [Finite A] (k : ℕ) (w v : List A) :
    tp k w = tp k v ↔
      ∀ φ : MSO A, φ.IsFO → φ.freeFO = ∅ → φ.qrank ≤ k →
        ((∀ fo so, MSO.Sat w fo so φ) ↔ (∀ fo so, MSO.Sat v fo so φ))

end Lax314295.KTypesFOEquivalence
end
