-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Basic

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

/-- The free second-order variables of a formula. -/
def freeSO : MSO A → Set ℕ
  | le _ _ => ∅
  | lab _ _ => ∅
  | mem _ j => {j}
  | not φ => freeSO φ
  | and φ ψ => freeSO φ ∪ freeSO ψ
  | or φ ψ => freeSO φ ∪ freeSO ψ
  | exFO _ φ => freeSO φ
  | exSO i φ => freeSO φ \ {i}

end MSO

open scoped Classical in
/-- The annotation `w ⊗ {x₁} ⊗ ⋯ ⊗ {x_k} ⊗ X₁ ⊗ ⋯ ⊗ X_l` of a string by the values
of `k` first-order and `l` second-order variables. -/
noncomputable def annotate {A : Type} (k l : ℕ) (w : List A)
    (fo : Fin k → ℕ) (so : Fin l → Set ℕ) : List (A × (Fin k → Bool) × (Fin l → Bool)) :=
  w.zipIdx.map (fun z => (z.1, fun i => decide (fo i = z.2), fun j => decide (z.2 ∈ so j)))

/-- Extend a valuation of the first-order variables `0, …, k-1` to all variables. -/
def extFO (k : ℕ) (fo : Fin k → ℕ) : ℕ → ℕ :=
  fun i => if h : i < k then fo ⟨i, h⟩ else 0

/-- Extend a valuation of the set variables `0, …, l-1` to all variables. -/
def extSO (l : ℕ) (so : Fin l → Set ℕ) : ℕ → Set ℕ :=
  fun j => if h : j < l then so ⟨j, h⟩ else ∅

end Lax314295.MSOLogic
end

-- Lax314295.MSOFreeVariables
section
namespace Lax314295.MSOFreeVariables

open Lax314295.MSOLogic

/-- The annotated strings satisfying a formula form a regular language. -/
axiom isRegular_annotated {A : Type} [Finite A] (φ : MSO A) (k l : ℕ)
    (hfo : φ.freeFO ⊆ {i | i < k}) (hso : φ.freeSO ⊆ {j | j < l}) :
    Language.IsRegular
      {u : List (A × (Fin k → Bool) × (Fin l → Bool)) |
        ∃ (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ),
          (∀ i, fo i < w.length) ∧ (∀ j, so j ⊆ {p | p < w.length}) ∧
          u = annotate k l w fo so ∧ MSO.Sat w (extFO k fo) (extSO l so) φ}

end Lax314295.MSOFreeVariables
end
