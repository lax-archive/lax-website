-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Computability.DFA
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Reduce
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

instance : Primcodable Input :=
  Primcodable.ofEquiv (ℕ × List (List ℕ) × List ℕ)
    { toFun := fun d => (d.predicates, d.transitions, d.accepting)
      invFun := fun (p, t, f) => ⟨p, t, f⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

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

-- Lax503819.Mortality
section
namespace Lax503819.Mortality

abbrev Instruction := ℕ × ℕ × Bool

structure Machine where
  statesMinusOne : ℕ
  symbolsMinusOne : ℕ
  table : List (List (Option Instruction))

instance : Primcodable Machine :=
  Primcodable.ofEquiv (ℕ × ℕ × List (List (Option Instruction)))
    { toFun := fun m => (m.statesMinusOne, m.symbolsMinusOne, m.table)
      invFun := fun (q, a, t) => ⟨q, a, t⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

structure Configuration where
  state : ℕ
  tape : List ℕ
  head : ℕ

def WellFormed (m : Machine) (c : Configuration) : Prop :=
  c.state < m.statesMinusOne + 1 ∧
  (∀ a ∈ c.tape, a < m.symbolsMinusOne + 1) ∧ c.head < c.tape.length

/-- A step on a finite tape; leaving its boundary halts. -/
def step (m : Machine) (c : Configuration) : Option Configuration := do
  let a ← c.tape[c.head]?
  let (q, b, right) ← (m.table.getD c.state []).getD a none
  if !right && c.head == 0 then none else
    let h := if right then c.head + 1 else c.head - 1
    if h < c.tape.length then
      some ⟨q % (m.statesMinusOne + 1),
        c.tape.set c.head (b % (m.symbolsMinusOne + 1)), h⟩
    else none

/-- After n attempts to take a step, `none` means that the run has halted. -/
def run (m : Machine) : ℕ → Configuration → Option Configuration
  | 0, c => some c
  | n + 1, c => (step m c).bind (run m n)

def Mortal (m : Machine) : Prop :=
  ∃ n : ℕ, ∀ c : Configuration, WellFormed m c → run m n c = none

end Lax503819.Mortality
end

-- Lax503819.Reduction
section
namespace Lax503819.Reduction

open Lax503819.Automata Lax503819.Mortality

axiom mortality_reduces :
  ∃ f : Machine → Input, Computable f ∧
    ∀ m, Mortal m ↔ PositiveDefinable (f m)

end Lax503819.Reduction
end
