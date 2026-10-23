-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.Language
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Forall2

-- Lax503819.Words
section
namespace Lax503819.Words

abbrev Position {A : Type} (w : List A) := Fin w.length

end Lax503819.Words
end

-- Lax503819.PositiveLogic
section
namespace Lax503819.PositiveLogic

open Lax503819.Words

inductive Formula (A : Type) : ℕ → Type where
  | truth {n} : Formula A n
  | falsity {n} : Formula A n
  | letter {n} : A → Fin n → Formula A n
  | le {n} : Fin n → Fin n → Formula A n
  | lt {n} : Fin n → Fin n → Formula A n
  | conj {n} : Formula A n → Formula A n → Formula A n
  | disj {n} : Formula A n → Formula A n → Formula A n
  | exists_ {n} : Formula A (n + 1) → Formula A n
  | forall_ {n} : Formula A (n + 1) → Formula A n

def Formula.Realize {A : Type} [LE A] {n : ℕ}
    (φ : Formula A n) (w : List A) (ρ : Fin n → Position w) : Prop :=
  match φ with
  | .truth => True
  | .falsity => False
  | .letter a x => a ≤ w.get (ρ x)
  | .le x y => ρ x ≤ ρ y
  | .lt x y => ρ x < ρ y
  | .conj φ ψ => φ.Realize w ρ ∧ ψ.Realize w ρ
  | .disj φ ψ => φ.Realize w ρ ∨ ψ.Realize w ρ
  | .exists_ φ => ∃ i : Position w, φ.Realize w (Fin.cons i ρ)
  | .forall_ φ => ∀ i : Position w, φ.Realize w (Fin.cons i ρ)

end Lax503819.PositiveLogic
end
