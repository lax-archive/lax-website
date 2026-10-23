-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Basic

-- Lax314295.MSOLogic
section
namespace Lax314295.MSOLogic.MSO.IsFO
end Lax314295.MSOLogic.MSO.IsFO

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

end MSO

end Lax314295.MSOLogic
end

-- Lax314295.MSORelabellings
section
namespace Lax314295.MSORelabellings

open Lax314295.MSOLogic

/-- An mso relabelling: a finite family of formulas with one free first-order
variable (the variable `0`), exactly one of which holds at each position of each
input, an output string for each formula, and an output for the empty input. -/
structure MSORelabelling (A B : Type) where
  /-- The index set of the formulas. -/
  Idx : Type
  /-- Finiteness of the index set. -/
  finIdx : Finite Idx
  /-- The formulas, each with the one free first-order variable `x₀`. -/
  form : Idx → MSO A
  /-- The output string of each formula. -/
  out : Idx → List B
  /-- The output string for the empty input. -/
  emptyOut : List B
  /-- At every position of every input string exactly one formula holds. -/
  unique : ∀ (w : List A) (p : ℕ), p < w.length →
    ∃! i : Idx, MSO.Sat w (fun _ => p) (fun _ => ∅) (form i)

namespace MSORelabelling

variable {A B : Type}

end MSORelabelling

end Lax314295.MSORelabellings
end
