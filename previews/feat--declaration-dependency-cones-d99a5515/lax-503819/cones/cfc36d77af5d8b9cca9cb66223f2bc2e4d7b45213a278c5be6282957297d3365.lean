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

def sentenceLanguage {A : Type} [LE A] (φ : Formula A 0) : Language A :=
  {w | φ.Realize w Fin.elim0}

def Definable {A : Type} [LE A] (L : Language A) : Prop :=
  ∃ φ : Formula A 0, sentenceLanguage φ = L

end Lax503819.PositiveLogic
end

-- Lax503819.PositiveGames
section
namespace Lax503819.PositiveGames

open Lax503819.Words Lax503819.PositiveLogic

def Valid {A : Type} [LE A] {u v : List A} {k : ℕ}
    (α : Fin k → Position u) (β : Fin k → Position v) : Prop :=
  (∀ i, u.get (α i) ≤ v.get (β i)) ∧
  (∀ i j, α i ≤ α j ↔ β i ≤ β j)

def Survives {A : Type} [LE A] (u v : List A) :
    ℕ → {k : ℕ} → (Fin k → Position u) → (Fin k → Position v) → Prop
  | 0, _, α, β => Valid α β
  | r + 1, _, α, β => Valid α β ∧
      (∀ x : Position u, ∃ y : Position v,
        Survives u v r (Fin.cons x α) (Fin.cons y β)) ∧
      (∀ y : Position v, ∃ x : Position u,
        Survives u v r (Fin.cons x α) (Fin.cons y β))

def DuplicatorWins {A : Type} [LE A] (r : ℕ) (u v : List A) : Prop :=
  Survives u v r (k := 0) Fin.elim0 Fin.elim0

axiom definable_iff_bounded_games {A : Type} [PartialOrder A] [Fintype A]
    (L : Language A) :
    Definable L ↔ ∃ r : ℕ, ∀ u v, u ∈ L → v ∉ L → ¬ DuplicatorWins r u v

end Lax503819.PositiveGames
end
