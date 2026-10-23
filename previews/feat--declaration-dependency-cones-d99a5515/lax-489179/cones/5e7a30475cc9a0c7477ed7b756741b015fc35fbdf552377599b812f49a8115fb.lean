-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.SetTheory.Cardinal.Finite

-- Lax489179.Satisfiability
section
namespace Lax489179.Satisfiability

abbrev Literal (n : ℕ) := Fin n × Bool

abbrev Clause (n : ℕ) := List (Literal n)

structure Formula where
  numVars : ℕ
  clauses : List (Clause numVars)

def Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Fin F.numVars → Bool,
    ∀ clause ∈ F.clauses, ∃ literal ∈ clause, assignment literal.1 = literal.2

def WidthAtMost (k : ℕ) (F : Formula) : Prop :=
  ∀ clause ∈ F.clauses, clause.length ≤ k

def encodeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

def encodeLiteral {n : ℕ} (literal : Literal n) : List Bool :=
  encodeNat literal.1.val ++ [literal.2]

def encodeClause {n : ℕ} (clause : Clause n) : List Bool :=
  encodeNat clause.length ++ clause.flatMap encodeLiteral

def encode (F : Formula) : List Bool :=
  encodeNat F.numVars ++ encodeNat F.clauses.length ++ F.clauses.flatMap encodeClause

end Lax489179.Satisfiability
end

-- Lax489179.Algorithms
section
namespace Lax489179.Algorithms

inductive Mode
  | deterministic
  | randomized
  deriving DecidableEq

/-- Deterministic mode restricts the program; randomized mode allows it. -/
def Allowed (mode : Mode) (isDeterministic : Prop) : Prop :=
  mode = .deterministic → isDeterministic

/-- Every random tape terminates, and at least two thirds return a
correct result. `none` means that the computation has not terminated. -/
def CorrectWithin {α : Type} (t : ℕ)
    (result : (Fin t → Bool) → Option α) (correct : α → Prop) : Prop :=
  (∀ r, (result r).isSome = true) ∧
  2 * 2 ^ t ≤ 3 * Nat.card {r : Fin t → Bool //
    ∃ y, result r = some y ∧ correct y}

end Lax489179.Algorithms
end

-- Lax489179.TuringMachine
section
namespace Lax489179.TuringMachine

inductive Move
  | left
  | stay
  | right

def Move.offset : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

inductive Instruction (tapes symbols states : ℕ)
  | halt (answer : Bool)
  | next (state : Fin states) (write : Fin tapes → Fin symbols)
      (move : Fin tapes → Move)

/-- The added constants ensure a nonempty control and tape set and
three distinct input/blank symbols. -/
structure Machine where
  tapes : ℕ
  symbols : ℕ
  states : ℕ
  transition : Fin (states + 1) → (Fin (tapes + 1) → Fin (symbols + 3)) →
    Bool → Instruction (tapes + 1) (symbols + 3) (states + 1)

structure Config (M : Machine) where
  state : Fin (M.states + 1)
  head : Fin (M.tapes + 1) → ℤ
  tape : Fin (M.tapes + 1) → ℤ → Fin (M.symbols + 3)
  answer : Option Bool

def init (M : Machine) (input : List Bool) : Config M where
  state := 0
  head := fun _ => 0
  tape := fun j z =>
    if j = 0 ∧ 0 ≤ z then
      match input[z.toNat]? with
      | none => 0
      | some false => 1
      | some true => 2
    else 0
  answer := none

/-- A halted configuration is unchanged, allowing a run to be padded. -/
def step (M : Machine) (coin : Bool) (c : Config M) : Config M :=
  match c.answer with
  | some _ => c
  | none =>
    match M.transition c.state (fun j => c.tape j (c.head j)) coin with
    | .halt b => { c with answer := some b }
    | .next q write move =>
      { state := q
        head := fun j => c.head j + (move j).offset
        tape := fun j z => if z = c.head j then write j else c.tape j z
        answer := none }

def run (M : Machine) : (t : ℕ) → (Fin t → Bool) → Config M → Config M
  | 0, _, c => c
  | t + 1, r, c => run M t (fun i => r i.succ) (step M (r 0) c)

def Deterministic (M : Machine) : Prop :=
  ∀ q scanned, M.transition q scanned false = M.transition q scanned true

def DecidesWithin (M : Machine) (input : List Bool) (answer : Prop) (t : ℕ) : Prop :=
  Algorithms.CorrectWithin t (fun r => (run M t r (init M input)).answer)
    (fun b => b = true ↔ answer)

end Lax489179.TuringMachine
end

-- Lax489179.SATTime
section
namespace Lax489179.SATTime

open Algorithms Satisfiability TuringMachine

def Solvable (mode : Mode) (k : ℕ) (a : ℝ) : Prop :=
  ∃ (M : Machine) (C : ℝ) (d : ℕ), 0 < C ∧ Allowed mode (Deterministic M) ∧
    ∀ F : Formula, WidthAtMost k F →
      ∃ t : ℕ, (t : ℝ) ≤ C * ((encode F).length + 1 : ℝ) ^ d *
        Real.rpow 2 (a * F.numVars) ∧
        DecidesWithin M (encode F) (Satisfiable F) t

end Lax489179.SATTime
end
