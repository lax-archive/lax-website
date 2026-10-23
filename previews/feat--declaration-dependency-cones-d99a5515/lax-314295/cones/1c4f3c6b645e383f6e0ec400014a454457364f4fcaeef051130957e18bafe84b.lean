-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Basic

-- Lax314295.MSOLogic
section
namespace Lax314295.MSOLogic.MSO.Sat
end Lax314295.MSOLogic.MSO.Sat

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

end MSO

end Lax314295.MSOLogic
end

-- Lax314295.MSOTransductions
section
namespace Lax314295.MSOTransductions.MSOTransduction.labRel
end Lax314295.MSOTransductions.MSOTransduction.labRel

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

/-- All formulas of the transduction are first-order. -/
def AllFO (T : MSOTransduction A B) : Prop :=
  (∀ i, (T.univP i).IsFO) ∧ (∀ j, (T.univC j).IsFO) ∧
  (∀ i b, (T.labP i b).IsFO) ∧ (∀ j b, (T.labC j b).IsFO) ∧
  (∀ i i', (T.ordPP i i').IsFO) ∧ (∀ i j, (T.ordPC i j).IsFO) ∧
  (∀ j i, (T.ordCP j i).IsFO) ∧ (∀ j j', (T.ordCC j j').IsFO)

end MSOTransduction

end Lax314295.MSOTransductions
end
