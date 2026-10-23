-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
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

-- Lax503819.Automata
section
namespace Lax503819.Automata

structure Input where
  predicates : ℕ
  transitions : List (List ℕ)
  accepting : List ℕ

abbrev Alphabet (d : Input) := Finset (Fin d.predicates)

/-- Binary column number of a subset of predicates. -/
def letterMask {p : ℕ} (a : Finset (Fin p)) : ℕ :=
  a.sum (fun i => 2 ^ i.val)

def Input.automaton (d : Input) : DFA (Alphabet d) (Fin (d.transitions.length + 1)) where
  step q a := Fin.ofNat (d.transitions.length + 1)
    ((d.transitions.getD q.val []).getD (letterMask a) 0)
  start := 0
  accept := {q | q.val ∈ d.accepting}

def Input.language (d : Input) : Language (Alphabet d) := d.automaton.accepts

def PositiveDefinable (d : Input) : Prop :=
  Lax503819.PositiveLogic.Definable d.language

end Lax503819.Automata
end
