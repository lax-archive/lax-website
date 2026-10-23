-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log
import Mathlib.SetTheory.Cardinal.Finite

-- Lax489179.IntegerEncoding
section
namespace Lax489179.IntegerEncoding.decodeOption
end Lax489179.IntegerEncoding.decodeOption

namespace Lax489179.IntegerEncoding

def encodeInt : ℤ → ℕ
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def encodeOption : Option ℤ → ℕ
  | none => 0
  | some z => encodeInt z + 1

end Lax489179.IntegerEncoding
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

-- Lax808846.Ram
section
namespace Lax808846.Ram.run
end Lax808846.Ram.run

namespace Lax808846.Ram

/-- An instruction. Every number naming a cell is read, except that
the first one names the destination for instructions that write a cell,
and the cell holding the destination address for `store`. `set` carries
a literal value; `jump`, `jzero`, and `jeof` carry program labels,
which are not data-memory addresses. -/
inductive Instr
  /-- Set cell `a` to the literal `n`. -/
  | set (a n : ℕ)
  /-- Set cell `a` to the contents of the cell whose address cell `b`
  holds. -/
  | load (a b : ℕ)
  /-- Set the cell whose address cell `a` holds to the contents of cell
  `b`. -/
  | store (a b : ℕ)
  /-- Set cell `a` to the sum of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | add (a b c : ℕ)
  /-- Set cell `a` to the difference of cells `b` and `c`, truncated at
  zero rather than wrapping around. -/
  | sub (a b c : ℕ)
  /-- Set cell `a` to the product of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | mul (a b c : ℕ)
  /-- Set cell `a` to the quotient of cells `b` and `c`, rounding
  towards zero; division by zero yields zero. -/
  | div (a b c : ℕ)
  /-- Set cell `a` to the bitwise conjunction of cells `b` and `c`. -/
  | and (a b c : ℕ)
  /-- Set cell `a` to cell `b` shifted left by the number of bits cell
  `c` holds, wrapping around modulo `2 ^ w`; a shift by `w` or more
  yields zero. -/
  | shiftl (a b c : ℕ)
  /-- Set cell `a` to the bitwise complement `2 ^ w - 1 - m[b]` of cell
  `b` within the word length. -/
  | not (a b : ℕ)
  /-- Continue at instruction `l`. -/
  | jump (l : ℕ)
  /-- Continue at instruction `l` if cell `a` is zero. -/
  | jzero (a l : ℕ)
  /-- Continue at instruction `l` exactly when the remaining input tape
  is empty. This test does not consume input. -/
  | jeof (l : ℕ)
  /-- Write the original input length, reduced to a word, into cell `a`. -/
  | inputLength (a : ℕ)
  /-- Read original input at the word index in cell `b` into cell `a`,
  returning zero outside the input. Read the index before writing `a`,
  even when the two cell addresses coincide. Do not consume input. -/
  | inputLoad (a b : ℕ)
  /-- Halt. -/
  | halt
  /-- Read the next number of the input tape into cell `a`, or halt if
  the tape is exhausted. -/
  | read (a : ℕ)
  /-- Append the contents of cell `a` to the output tape. -/
  | write (a : ℕ)

/-- A machine state: the program counter, the contents of every memory
cell, the immutable original input array, the remaining sequential input
tape, and the output tape written so far. -/
structure State where
  /-- The number of the instruction to be executed next. -/
  pc : ℕ
  /-- The contents of the memory cells; only the cells with number below
  `2 ^ w` are ever addressed. -/
  mem : ℕ → ℕ
  /-- The original read-only input, unchanged by every instruction. -/
  input : List ℕ
  /-- The numbers still to be read from the input tape. -/
  inp : List ℕ
  /-- The numbers written to the output tape so far. -/
  out : List ℕ

/-- The memory `m` with cell `a` set to `v`, at word length `w`: the
address and the value written are both taken modulo `2 ^ w`. -/
def setCell (w : ℕ) (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ :=
  fun b => if b = a % 2 ^ w then v % 2 ^ w else m b

/-- The effect of one instruction on the state at word length `w`, or
`none` if it halts the machine, which a `halt` instruction and a read
from an exhausted input tape do. Data values, input indices, and
data-memory addresses are reduced modulo `2 ^ w`; program labels and
the counter are not. -/
def Instr.effect (w : ℕ) : Instr → State → Option State
  | set a n, s => some { s with pc := s.pc + 1, mem := setCell w s.mem a n }
  | load a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (s.mem (b % 2 ^ w) % 2 ^ w)) }
  | store a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem (s.mem (a % 2 ^ w)) (s.mem (b % 2 ^ w)) }
  | add a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) + s.mem (c % 2 ^ w)) }
  | sub a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) - s.mem (c % 2 ^ w)) }
  | mul a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * s.mem (c % 2 ^ w)) }
  | div a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) / s.mem (c % 2 ^ w)) }
  | and a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (Nat.land (s.mem (b % 2 ^ w)) (s.mem (c % 2 ^ w))) }
  | shiftl a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * 2 ^ s.mem (c % 2 ^ w)) }
  | not a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (2 ^ w - 1 - s.mem (b % 2 ^ w)) }
  | jump l, s => some { s with pc := l }
  | jzero a l, s => some { s with pc := if s.mem (a % 2 ^ w) = 0 then l else s.pc + 1 }
  | jeof l, s => some { s with pc := if s.inp.isEmpty then l else s.pc + 1 }
  | inputLength a, s =>
      some { s with pc := s.pc + 1, mem := setCell w s.mem a s.input.length }
  | inputLoad a b, s =>
      some { s with
        pc := s.pc + 1
        mem := setCell w s.mem a (s.input[s.mem (b % 2 ^ w) % 2 ^ w]?.getD 0) }
  | halt, _ => none
  | read a, s =>
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := setCell w s.mem a v, inp := s.inp.tail }
  | write a, s =>
      some { s with pc := s.pc + 1, out := s.out ++ [s.mem (a % 2 ^ w) % 2 ^ w] }

/-- The initial state on input `x`: program counter zero, all memory
cells zero, the original input array and its sequential tape both `x`,
and the output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  mem := fun _ => 0
  input := x
  inp := x
  out := []

end Lax808846.Ram
end

-- Lax489179.WordPrograms
section
namespace Lax489179.WordPrograms

open Lax808846.Ram

inductive Instruction
  | ordinary (instruction : Instr)
  | coin (destination : ℕ)

abbrev Program := List Instruction

structure Config where
  state : State
  halted : Bool

def init (input : List ℕ) : Config := ⟨initState input, false⟩

def step (w : ℕ) (p : Program) (bit : Bool) (c : Config) : Config :=
  if c.halted then c else
    match p[c.state.pc]? with
    | none => { c with halted := true }
    | some (.ordinary instruction) =>
      match instruction.effect w c.state with
      | none => { c with halted := true }
      | some s => ⟨s, false⟩
    | some (.coin a) =>
      ⟨{ c.state with
          pc := c.state.pc + 1
          mem := setCell w c.state.mem a bit.toNat }, false⟩

def run (w : ℕ) (p : Program) : (t : ℕ) → (Fin t → Bool) → Config → Config
  | 0, _, c => c
  | t + 1, r, c => run w p t (fun i => r i.succ) (step w p (r 0) c)

def output (c : Config) : Option (List ℕ) :=
  if c.halted then some c.state.out else none

def Deterministic (p : Program) : Prop :=
  ∀ a, Instruction.coin a ∉ p

def ComputesWithin (w : ℕ) (p : Program) (input : List ℕ)
    (correct : List ℕ → Prop) (t : ℕ) : Prop :=
  Algorithms.CorrectWithin t (fun r => output (run w p t r (init input))) correct

end Lax489179.WordPrograms
end

-- Lax489179.WordTime
section
namespace Lax489179.WordTime

structure Problem where
  Input : Type
  size : Input → ℕ
  encode : Input → List ℕ
  valid : Input → Prop
  correct : Input → List ℕ → Prop

def wordLength (b n : ℕ) : ℕ := b * (Nat.log2 (n + 2) + 1)

def Fits (w : ℕ) (input : List ℕ) : Prop :=
  input.length < 2 ^ w ∧ ∀ x ∈ input, x < 2 ^ w

def Solvable (mode : Algorithms.Mode) (P : Problem) (a : ℝ) : Prop :=
  ∃ (p : WordPrograms.Program) (b : ℕ) (C : ℝ),
    0 < b ∧ 0 < C ∧ Algorithms.Allowed mode (WordPrograms.Deterministic p) ∧
    ∀ x : P.Input, P.valid x →
      Fits (wordLength b (P.size x)) (P.encode x) ∧
      ∃ t : ℕ, (t : ℝ) ≤ C * Real.rpow (P.size x + 2 : ℝ) a ∧
        WordPrograms.ComputesWithin (wordLength b (P.size x)) p
          (P.encode x) (P.correct x) t

end Lax489179.WordTime
end

-- Lax489179.WeightedAPSP
section
namespace Lax489179.WeightedAPSP

structure Graph where
  vertices : ℕ
  edge : Fin vertices → Fin vertices → Option ℤ

inductive Walk (G : Graph) : Fin G.vertices → Fin G.vertices → ℤ → Prop
  | nil (v : Fin G.vertices) : Walk G v v 0
  | cons {u v z : Fin G.vertices} {a b : ℤ}
      (edge : G.edge u v = some a) (tail : Walk G v z b) : Walk G u z (a + b)

def NoNegativeCycle (G : Graph) : Prop :=
  ∀ v d, Walk G v v d → 0 ≤ d

def BoundedWeights (c : ℕ) (G : Graph) : Prop :=
  ∀ u v z, G.edge u v = some z → z.natAbs ≤ G.vertices ^ c

def Distance (G : Graph) (u v : Fin G.vertices) : Option ℤ → Prop
  | none => ¬ ∃ d, Walk G u v d
  | some d => Walk G u v d ∧ ∀ d', Walk G u v d' → d ≤ d'

def encodeMatrix (n : ℕ) (matrix : Fin n → Fin n → Option ℤ) : List ℕ :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => IntegerEncoding.encodeOption (matrix i j)

def encode (G : Graph) : List ℕ := G.vertices :: encodeMatrix G.vertices G.edge

def Correct (G : Graph) (output : List ℕ) : Prop :=
  ∃ matrix : Fin G.vertices → Fin G.vertices → Option ℤ,
    output = encodeMatrix G.vertices matrix ∧ ∀ u v, Distance G u v (matrix u v)

def problem (c : ℕ) : WordTime.Problem where
  Input := Graph
  size := Graph.vertices
  encode := encode
  valid := fun G => BoundedWeights c G ∧ NoNegativeCycle G
  correct := Correct

end Lax489179.WeightedAPSP
end

-- Lax489179.APSPHypothesis
section
namespace Lax489179.APSPHypothesis

def HypothesisAt (mode : Algorithms.Mode) (c : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ¬ WordTime.Solvable mode (WeightedAPSP.problem c) (3 - ε)

def Hypothesis (mode : Algorithms.Mode) : Prop :=
  ∃ c : ℕ, 0 < c ∧ HypothesisAt mode c

def Randomized : Prop := Hypothesis .randomized

end Lax489179.APSPHypothesis
end
