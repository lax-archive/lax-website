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

-- Lax314295.MSOTransductions
section
namespace Lax314295.MSOTransductions.MSOTransduction.ordRel
end Lax314295.MSOTransductions.MSOTransduction.ordRel

namespace Lax314295.MSOTransductions.MSOTransduction.selected
end Lax314295.MSOTransductions.MSOTransduction.selected

namespace Lax314295.MSOTransductions

open Lax314295.MSOLogic

/-- A string-to-string mso transduction of the linear type `copies · n + extra`,
presented by families of ordinary mso formulas indexed by the variants of the
type. -/
structure MSOTransduction (A B : Type) where
  /-- The number of copies of the input positions. -/
  copies : ℕ
  /-- The number of extra (constant) elements. -/
  extra : ℕ
  /-- Universe formulas for the copies of the positions; free variable `x₀`. -/
  univP : Fin copies → MSO A
  /-- Universe formulas for the extra elements; sentences. -/
  univC : Fin extra → MSO A
  /-- Letter formulas for the copies of the positions; free variable `x₀`. -/
  labP : Fin copies → B → MSO A
  /-- Letter formulas for the extra elements; sentences. -/
  labC : Fin extra → B → MSO A
  /-- Order formulas between two copies of positions; free variables `x₀, x₁`. -/
  ordPP : Fin copies → Fin copies → MSO A
  /-- Order formulas between a copy of a position and an extra element. -/
  ordPC : Fin copies → Fin extra → MSO A
  /-- Order formulas between an extra element and a copy of a position. -/
  ordCP : Fin extra → Fin copies → MSO A
  /-- Order formulas between two extra elements. -/
  ordCC : Fin extra → Fin extra → MSO A

namespace MSOTransduction

variable {A B : Type}

/-- The elements of the type `copies · n + extra`, before selection. -/
abbrev Elt (T : MSOTransduction A B) : Type := (Fin T.copies × ℕ) ⊕ Fin T.extra

/-- The labelling defined by the letter formulas. -/
def labRel (T : MSOTransduction A B) (w : List A) : T.Elt → B → Prop
  | Sum.inl (i, p), b => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.labP i b)
  | Sum.inr j, b => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.labC j b)

end MSOTransduction

end Lax314295.MSOTransductions
end
