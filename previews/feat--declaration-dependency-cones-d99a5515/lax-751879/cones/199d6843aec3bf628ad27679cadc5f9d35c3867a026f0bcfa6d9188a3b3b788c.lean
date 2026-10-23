-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange

-- Lax751879.OrderedStructures
section
namespace Lax751879.OrderedStructures.OrderedStructure
end Lax751879.OrderedStructures.OrderedStructure

namespace Lax751879.OrderedStructures.PointedStructure
end Lax751879.OrderedStructures.PointedStructure

namespace Lax751879.OrderedStructures

abbrev Vocabulary := List Nat

/-- Relation symbols are numbered in the order of the vocabulary. -/
abbrev Symbol (σ : Vocabulary) := Fin σ.length

end Lax751879.OrderedStructures
end

-- Lax751879.FixedPointSyntax
section
namespace Lax751879.FixedPointSyntax

open Lax751879.OrderedStructures

inductive RawFormula (σ : Vocabulary) : Nat → List Nat → Type
  | truth {m ρ} : RawFormula σ m ρ
  | equal {m ρ} (x y : Fin m) : RawFormula σ m ρ
  | less {m ρ} (x y : Fin m) : RawFormula σ m ρ
  | relation {m ρ} (r : Symbol σ) (args : Fin (σ.get r) → Fin m) :
      RawFormula σ m ρ
  | variable {m ρ} (r : Fin ρ.length) (args : Fin (ρ.get r) → Fin m) :
      RawFormula σ m ρ
  | neg {m ρ} (φ : RawFormula σ m ρ) : RawFormula σ m ρ
  | conj {m ρ} (φ ψ : RawFormula σ m ρ) : RawFormula σ m ρ
  | exists' {m ρ} (φ : RawFormula σ (m + 1) ρ) : RawFormula σ m ρ
  | lfp {m ρ} (k : Nat) (body : RawFormula σ (k + m) (k :: ρ))
      (args : Fin k → Fin m) : RawFormula σ m ρ

/-- Every occurrence of `r` has the required polarity. `true` means positive. -/
def RawFormula.positiveAt {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) (r : Fin ρ.length) (polarity : Bool) : Prop :=
  match φ with
  | .truth | .equal _ _ | .less _ _ | .relation _ _ => True
  | .variable s _ => s = r → polarity = true
  | .neg ψ => ψ.positiveAt r (!polarity)
  | .conj ψ χ => ψ.positiveAt r polarity ∧ χ.positiveAt r polarity
  | .exists' ψ => ψ.positiveAt r polarity
  | .lfp _ body _ => body.positiveAt r.succ polarity

/-- Every fixed-point binder has a positive defining body. -/
def RawFormula.Admissible {σ : Vocabulary} {m : Nat} {ρ : List Nat}
    (φ : RawFormula σ m ρ) : Prop :=
  match φ with
  | .truth | .equal _ _ | .less _ _ | .relation _ _ | .variable _ _ => True
  | .neg ψ | .exists' ψ => ψ.Admissible
  | .conj ψ χ => ψ.Admissible ∧ χ.Admissible
  | .lfp _ body _ => body.Admissible ∧ body.positiveAt 0 true

abbrev Formula (σ : Vocabulary) (m : Nat) :=
  {φ : RawFormula σ m [] // φ.Admissible}

end Lax751879.FixedPointSyntax
end
