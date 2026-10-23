-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.DeriveFintype

-- Lax560851.StructuralPresentation
section
namespace Lax560851.StructuralPresentation.Raw.nodes
end Lax560851.StructuralPresentation.Raw.nodes

namespace Lax560851.StructuralPresentation

universe u

/-- The universal shape of structurally finite data. -/
inductive Raw where
  | nat : Nat → Raw
  | pair : Raw → Raw → Raw
  deriving DecidableEq

namespace Raw

end Raw

/-- An encoder into the universal shape and a partial inverse. -/
structure Presentation (α : Type u) where
  toRaw : α → Raw
  fromRaw : Raw → Option α

/-- Package an injective structural map as a low-level presentation by
choosing a preimage on its range. This construction certifies no complexity
or constructor-structurality property of the supplied map. -/
noncomputable def presentationOf {α : Type u} (f : α → Raw) : Presentation α := by
  classical
  exact {
    toRaw := f
    fromRaw := fun raw =>
      if h : ∃ x, f x = raw then some (Classical.choose h) else none
  }

namespace Presentation

/-- Distinct values have distinct structural representations. -/
def Faithful {α : Type u} (P : Presentation α) : Prop :=
  Function.Injective P.toRaw

end Presentation

end Lax560851.StructuralPresentation
end

-- Lax560851.WordArena
section
namespace Lax560851.WordArena.WordImage.ChildAddress
end Lax560851.WordArena.WordImage.ChildAddress

namespace Lax560851.WordArena.WordImage.ReachableFrom
end Lax560851.WordArena.WordImage.ReachableFrom

namespace Lax560851.WordArena.WordImage.Represents
end Lax560851.WordArena.WordImage.Represents

namespace Lax560851.WordArena

open Lax560851.StructuralPresentation

universe u

/-- A finite array of unbounded natural-number words. -/
abbrev WordMemory := Array Nat

/-- A closed word array together with its distinguished root address. -/
structure WordImage where
  memory : WordMemory
  root : Nat
  deriving DecidableEq

namespace WordImage

/-- The distinguished Lax808846 input tape: root, followed by all arena words. -/
def toInput (I : WordImage) : List Nat := I.root :: I.memory.toList

/-- Tag of a natural-payload block. -/
def natTag : Nat := 0

/-- Tag of a binary-pair block. -/
def pairTag : Nat := 1

end WordImage

/-- Append the postorder arena of a raw value and return its root address. -/
def encodeInto : Raw → WordMemory → WordMemory × Nat
  | .nat payload, memory =>
      let address := memory.size
      (memory.push WordImage.natTag |>.push payload |>.push 0, address)
  | .pair left right, memory =>
      let (memory, leftAddress) := encodeInto left memory
      let (memory, rightAddress) := encodeInto right memory
      let address := memory.size
      (memory.push WordImage.pairTag |>.push leftAddress |>.push rightAddress, address)

/-- Distinguished closed postorder arena of a structural value. -/
def encodeRaw (raw : Raw) : WordImage :=
  let (memory, root) := encodeInto raw #[]
  { memory, root }

/-- Distinguished arena of a value through a named structural presentation. -/
def encode {α : Type u} (P : Presentation α) (x : α) : WordImage :=
  encodeRaw (P.toRaw x)

end Lax560851.WordArena
end

-- Lax759944.BinaryWordEncoding
section
set_option backward.isDefEq.respectTransparency false

namespace Lax759944.BinaryWordEncoding

/-- The finite alphabet used to encode lists of natural numbers. -/
inductive Symbol
  | separator
  | zero
  | one
  deriving DecidableEq, Fintype, Inhabited

/-- Encode one natural number, including the separator which begins it. -/
def encodeNat (n : ℕ) : List Symbol :=
  .separator :: n.bits.map (fun b => if b then .one else .zero)

/-- The canonical binary encoding of a finite list of natural numbers. -/
def encode (x : List ℕ) : List Symbol :=
  x.flatMap encodeNat

/-- The bit-size of a finite list of natural numbers. -/
def bitSize (x : List ℕ) : ℕ :=
  (encode x).length

end Lax759944.BinaryWordEncoding
end

-- Lax213208.OptimizationProblem
section
namespace Lax213208.OptimizationProblem

open scoped NNReal

open Lax560851.StructuralPresentation Lax560851.WordArena

open Lax759944.BinaryWordEncoding

inductive Direction
  | minimize
  | maximize

structure Problem (Instance Solution : Type*) where
  direction : Direction
  feasible : Instance → Solution → Prop
  value : Instance → Solution → ℝ≥0
  input : Presentation Instance
  output : Solution → List ℕ
  input_faithful : input.Faithful
  output_injective : Function.Injective output

variable {Instance Solution : Type*}

def inputWords (problem : Problem Instance Solution) (x : Instance) : List ℕ :=
  (encode problem.input x).toInput

def inputSize (problem : Problem Instance Solution) (x : Instance) : ℕ :=
  bitSize (inputWords problem x)

end Lax213208.OptimizationProblem
end

-- Lax560851.StructuralCombinators
section
namespace Lax560851.StructuralCombinators.Derivable
end Lax560851.StructuralCombinators.Derivable

namespace Lax560851.StructuralCombinators.Generated
end Lax560851.StructuralCombinators.Generated

namespace Lax560851.StructuralCombinators.Lawful
end Lax560851.StructuralCombinators.Lawful

namespace Lax560851.StructuralCombinators.SizeLaws
end Lax560851.StructuralCombinators.SizeLaws

namespace Lax560851.StructuralCombinators.listFromRaw
end Lax560851.StructuralCombinators.listFromRaw

namespace Lax560851.StructuralCombinators.Raw.constructorCharsCode
end Lax560851.StructuralCombinators.Raw.constructorCharsCode

namespace Lax560851.StructuralCombinators.Raw.fields
end Lax560851.StructuralCombinators.Raw.fields

namespace Lax560851.StructuralCombinators

open Lax560851.StructuralPresentation

open Lax560851.StructuralPresentation.Presentation

universe u v

namespace Raw

end Raw

/-- Structural presentation of natural numbers. -/
def nat : Presentation Nat where
  toRaw := .nat
  fromRaw
    | .nat n => some n
    | _ => none

/-- Structural presentation of a product. -/
def prod {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    Presentation (α × β) where
  toRaw x := .pair (A.toRaw x.1) (B.toRaw x.2)
  fromRaw
    | .pair a b =>
        match A.fromRaw a with
        | none => none
        | some x =>
            match B.fromRaw b with
            | none => none
            | some y => some (x, y)
    | _ => none

/-- Universal structural representation of a list. -/
def listToRaw {α : Type u} (P : Presentation α) : List α → StructuralPresentation.Raw
  | [] => .nat 0
  | x :: xs => .pair (P.toRaw x) (listToRaw P xs)

end Lax560851.StructuralCombinators
end

-- Lax213208.AlgorithmInput
section
namespace Lax213208.AlgorithmInput

open OptimizationProblem

open Lax560851.WordArena Lax560851.StructuralCombinators

variable {Instance Solution : Type*}

def inputTape (problem : Problem Instance Solution)
    (precision : Option ℕ) (x : Instance) : List ℕ :=
  match precision with
  | none => inputWords problem x
  | some k => (encode (prod nat problem.input) (k, x)).toInput

end Lax213208.AlgorithmInput
end

-- Lax213208.Approximation
section
namespace Lax213208.Approximation

open OptimizationProblem

variable {Instance Solution : Type*}

def IsApproximation (problem : Problem Instance Solution)
    (r : ℝ) (x : Instance) (y : Solution) : Prop :=
  1 ≤ r ∧ problem.feasible x y ∧ ∀ z, problem.feasible x z →
    match problem.direction with
    | .minimize => (problem.value x y : ℝ) ≤ r * problem.value x z
    | .maximize => (problem.value x z : ℝ) ≤ r * problem.value x y

end Lax213208.Approximation
end

-- Lax808846.Ram
section
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

/-- A program: a finite sequence of instructions, numbered from `0`. -/
abbrev Program : Type := List Instr

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

/-- One step of the machine at word length `w`: fetch the instruction
the program counter points at and execute it. The result is `none` if
the machine has halted, which also happens when the program counter has
run past the program. -/
def step (w : ℕ) (p : Program) (s : State) : Option State :=
  p[s.pc]?.bind fun i => i.effect w s

/-- The state after `t` successful transitions at word length `w`, or
`none` if one of those transitions terminates. This auxiliary count does
not include a fetched terminal instruction; `RunsTo` charges that too. -/
def run (w : ℕ) (p : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step w p s).bind (run w p t)

/-- The initial state on input `x`: program counter zero, all memory
cells zero, the original input array and its sequential tape both `x`,
and the output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  mem := fun _ => 0
  input := x
  inp := x
  out := []

/-- Cost of termination at `s`, when `step w p s = none`: a fetched
terminal instruction costs one, while an out-of-range program counter
costs zero because there is no instruction to execute. -/
def terminalCost (p : Program) (s : State) : ℕ :=
  if s.pc < p.length then 1 else 0

/-- Started on input `x` at word length `w`, the machine executes
exactly `t` instructions and then halts, having written the word `y` to
its output tape. -/
def RunsTo (w : ℕ) (p : Program) (x y : List ℕ) (t : ℕ) : Prop :=
  ∃ (k : ℕ) (s : State), run w p k (initState x) = some s ∧
    step w p s = none ∧ s.out = y ∧ t = k + terminalCost p s

end Lax808846.Ram
end

-- Lax759944.RamPolytime
section
namespace Lax759944.RamPolytime

open Lax808846.Ram

open Lax759944.BinaryWordEncoding

/-- Every entry of `x` is representable by a word of `w` bits. -/
def FitsInWords (w : ℕ) (x : List ℕ) : Prop :=
  ∀ a ∈ x, a < 2 ^ w

end Lax759944.RamPolytime
end

-- Lax808846.RamComputes
section
namespace Lax808846.RamComputes

open Lax808846.Ram

/-- At word length `w`, on every admissible input `x`, the program halts
within `T x` executed instructions with output `f x`. -/
def ComputesInTime (w : ℕ) (p : Program) (D : Set (List ℕ))
    (f : List ℕ → List ℕ) (T : List ℕ → ℕ) : Prop :=
  ∀ x ∈ D, ∃ t ≤ T x, RunsTo w p x (f x) t

end Lax808846.RamComputes
end

-- Lax213208.Programs
section
namespace Lax213208.Programs

open Lax808846.Ram Lax808846.RamComputes Lax759944.RamPolytime

abbrev Program := Lax808846.Ram.Program

def Returns (alg : Program) (input output : List ℕ) : Prop :=
  ∃ width : ℕ, ∀ w ≥ width, ∃ steps, RunsTo w alg input output steps

def RunsWithin (alg : Program) (input output : List ℕ) (bound : ℕ) : Prop :=
  FitsInWords bound (input.length :: input) ∧
    ∀ w ≥ bound, ComputesInTime w alg {input} (fun _ => output) (fun _ => bound)

end Lax213208.Programs
end

-- Lax213208.RApproximation
section
namespace Lax213208.RApproximation

open OptimizationProblem Approximation AlgorithmInput Programs

variable {Instance Solution : Type*} {problem : Problem Instance Solution}

def Approximates (alg : Program) (inputs : Set Instance) (r : ℝ)
    (precision : Option ℕ := none) : Prop :=
  1 ≤ r ∧ ∀ x ∈ inputs, ∃ y,
    Returns alg (inputTape problem precision x) (problem.output y) ∧
    IsApproximation problem r x y

end Lax213208.RApproximation
end

-- Lax213208.RunningTime
section
namespace Lax213208.RunningTime

open OptimizationProblem AlgorithmInput Programs

variable {Instance Solution : Type*} {problem : Problem Instance Solution}

def RunsInTime (alg : Program) (inputs : Set Instance) (time : ℕ → ℕ)
    (precision : Option ℕ := none) : Prop :=
  ∀ x ∈ inputs, ∃ output,
    RunsWithin alg (inputTape problem precision x) output (time (inputSize problem x))

def QuasipolynomialTime (alg : Program) (inputs : Set Instance)
    (precision : Option ℕ := none) : Prop :=
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    RunsInTime (problem := problem) alg inputs
      (fun n => 2 ^ (c * (Nat.log2 (n + 2) + 1) ^ d)) precision

end Lax213208.RunningTime
end

-- Lax213208.QPTAS
section
namespace Lax213208.QPTAS

open OptimizationProblem Programs RApproximation RunningTime

variable {Instance Solution : Type*} {problem : Problem Instance Solution}

def QPTAS (alg : Program) (inputs : Set Instance) : Prop :=
  ∀ k : ℕ, 0 < k →
    let ε : ℝ := 1 / k
    Approximates (problem := problem) alg inputs (1 + ε) (some k) ∧
    QuasipolynomialTime (problem := problem) alg inputs (some k)

end Lax213208.QPTAS
end

-- Lax263307.GraphClasses
section
namespace Lax263307.GraphClasses

/-- A class of finite simple graphs, represented on numbered vertex sets. -/
abbrev GraphClass := (n : ℕ) → Set (SimpleGraph (Fin n))

/-- Every graph that embeds as an induced subgraph of a member also belongs. -/
def IsHereditary (C : GraphClass) : Prop :=
  ∀ (m n : ℕ) (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)),
    G ∈ C n → Nonempty (H ↪g G) → H ∈ C m

end Lax263307.GraphClasses
end

-- Lax263307.EdgeSublinearSeparators
section
namespace Lax263307.EdgeSublinearSeparators

open GraphClasses

/-- Each component after deleting `S` contains at most two thirds of the vertices. -/
def IsBalancedSeparator {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Prop :=
  ∀ K : (G.induce (↑S : Set (Fin n))ᶜ).ConnectedComponent,
    3 * K.supp.ncard ≤ 2 * n

/-- A uniform separator bound sublinear in the number of edges. -/
def HasStronglyEdgeSublinearSeparators (C : GraphClass) : Prop :=
  ∃ (b c : ℝ), 0 ≤ b ∧ b < 1 ∧ 0 < c ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ C n →
      ∃ S : Finset (Fin n), IsBalancedSeparator G S ∧
        (S.card : ℝ) ≤ c * Real.rpow ((G.edgeSet.ncard : ℝ) + 1) b

end Lax263307.EdgeSublinearSeparators
end

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307.WeightedIndependentSet

/-- A finite graph with rational vertex weights. -/
structure Instance where
  order : ℕ
  graph : SimpleGraph (Fin order)
  weights : Fin order → ℚ

/-- A vertex set in an explicitly specified finite ambient set. -/
abbrev Solution := (n : ℕ) × Finset (Fin n)

/-- Total weight of a vertex set. -/
def weight {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : ℚ :=
  ∑ v ∈ I, w v

end Lax263307.WeightedIndependentSet
end

-- Lax263307.IndependentSetEncoding
section
namespace Lax263307.IndependentSetEncoding

open WeightedIndependentSet

open Lax560851.StructuralPresentation Lax560851.StructuralCombinators

open Lax759944.BinaryWordEncoding (bitSize)

open scoped Classical

/-- Canonical sign, absolute numerator, and denominator of a rational. -/
def encodeRational (q : ℚ) : List ℕ :=
  [if q.num < 0 then 1 else 0, q.num.natAbs, q.den]

/-- The length-`n` membership vector of the selected independent set. -/
def encodeOutput {n : ℕ} (I : Finset (Fin n)) : List ℕ :=
  List.ofFn fun v => if v ∈ I then 1 else 0

/-- Canonical graph-and-weight packet, without the accuracy parameter. -/
noncomputable abbrev encodeInstance {n : ℕ} (G : SimpleGraph (Fin n))
    (w : Fin n → ℚ) : List ℕ :=
  [n] ++ (List.ofFn fun u => List.ofFn fun v =>
    if G.Adj u v then 1 else 0).flatten ++
    (List.ofFn w).flatMap encodeRational

/-- Equal-length blocks can be separated without interpreting their contents. -/
private theorem blocks_injective {α β : Type*} (f : α → List β) (k : ℕ)
    (length : ∀ a, (f a).length = k) (injective : Function.Injective f) :
    ∀ xs ys : List α, xs.length = ys.length → xs.flatMap f = ys.flatMap f → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | x :: xs, y :: ys, hlength, h =>
      let fields := List.append_inj h ((length x).trans (length y).symm)
      congrArg₂ List.cons (injective fields.1)
        (blocks_injective f k length injective xs ys (Nat.succ.inj hlength) fields.2)

private theorem blocks_length {α β : Type*} (f : α → List β) (k : ℕ)
    (length : ∀ a, (f a).length = k) (xs : List α) :
    (xs.flatMap f).length = xs.length * k :=
  calc
    (xs.flatMap f).length = (xs.map fun a => (f a).length).sum := List.length_flatMap
    _ = (xs.map fun _ => k).sum := congrArg (fun g => (xs.map g).sum) (funext length)
    _ = (List.replicate xs.length k).sum := congrArg List.sum List.map_const
    _ = xs.length * k := List.sum_replicate _ _

private theorem flag_injective (p q : Prop) [Decidable p] [Decidable q]
    (h : (if p then 1 else 0 : ℕ) = if q then 1 else 0) : p ↔ q :=
  ⟨fun hp => not_not.mp (fun hq => Nat.one_ne_zero
      ((if_pos hp).symm.trans (h.trans (if_neg hq)))),
   fun hq => not_not.mp (fun hp => Nat.one_ne_zero
      ((if_pos hq).symm.trans (h.symm.trans (if_neg hp))))⟩

private theorem signed_integer_injective : ∀ a b : ℤ,
    (if a < 0 then 1 else 0 : ℕ) = (if b < 0 then 1 else 0) →
    a.natAbs = b.natAbs → a = b
  | .ofNat _, .ofNat _, _, habs => congrArg Int.ofNat habs
  | .negSucc _, .negSucc _, _, habs => congrArg Int.negSucc (Nat.succ.inj habs)
  | .ofNat a, .negSucc b, hsign, _ => False.elim (Nat.zero_ne_one
      ((if_neg (not_lt.mpr (Int.natCast_nonneg a))).symm.trans
        (hsign.trans (if_pos (Int.negSucc_lt_zero b)))))
  | .negSucc a, .ofNat b, hsign, _ => False.elim (Nat.one_ne_zero
      ((if_pos (Int.negSucc_lt_zero a)).symm.trans
        (hsign.trans (if_neg (not_lt.mpr (Int.natCast_nonneg b))))))

private theorem rational_injective : Function.Injective encodeRational :=
  fun a b h =>
    let fields := List.cons.inj h
    let rest := List.cons.inj fields.2
    Rat.ext (signed_integer_injective a.num b.num fields.1 rest.1)
      (List.cons.inj rest.2).1

private theorem matrix_blocks {n : ℕ} (G : SimpleGraph (Fin n)) :
    (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten =
      (List.ofFn fun u v => if G.Adj u v then 1 else 0).flatMap List.ofFn :=
  (congrArg List.flatten (List.map_ofFn (f := fun (u v : Fin n) => (if G.Adj u v then 1 else 0 : ℕ))
    (g := fun f : Fin n → ℕ => List.ofFn f))).symm

private theorem matrix_length {n : ℕ} (G : SimpleGraph (Fin n)) :
    (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten.length = n*n :=
  (congrArg List.length (matrix_blocks G)).trans
    ((blocks_length List.ofFn n (fun _ => List.length_ofFn) _).trans
      (congrArg (· * n) List.length_ofFn))

private theorem matrix_injective {n : ℕ} (G H : SimpleGraph (Fin n))
    (h : (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten =
      (List.ofFn fun u => List.ofFn fun v => if H.Adj u v then 1 else 0).flatten) : G = H :=
  let rows := blocks_injective List.ofFn n (fun _ => List.length_ofFn)
    List.ofFn_injective _ _ (List.length_ofFn.trans List.length_ofFn.symm)
    ((matrix_blocks G).symm.trans (h.trans (matrix_blocks H)))
  SimpleGraph.ext (funext fun u => funext fun v => propext
    (flag_injective _ _ (congrFun (congrFun (List.ofFn_injective rows) u) v)))

private theorem weights_injective {n : ℕ} (w z : Fin n → ℚ)
    (h : (List.ofFn w).flatMap encodeRational = (List.ofFn z).flatMap encodeRational) : w = z :=
  List.ofFn_injective (blocks_injective encodeRational 3 (fun _ => rfl)
    rational_injective _ _ (List.length_ofFn.trans List.length_ofFn.symm) h)

/-- The canonical packet determines all three mathematical instance fields. -/
private theorem encodeInstance_injective : Function.Injective
    (fun x : Instance => encodeInstance x.graph x.weights) :=
  fun x y h =>
    let order : x.order = y.order := (List.cons.inj h).1
    match x, y, order, h with
    | ⟨n,G,w⟩, ⟨_,H,z⟩, rfl, h =>
      let fields := List.append_inj (List.cons.inj h).2
        ((matrix_length G).trans (matrix_length H).symm)
      congrArg₂ (Instance.mk n) (matrix_injective G H fields.1) (weights_injective w z fields.2)

private theorem list_injective :
    ∀ xs ys : List ℕ, listToRaw nat xs = listToRaw nat ys → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: xs, _ :: ys, h =>
      let fields := Lax560851.StructuralPresentation.Raw.pair.inj h
      congrArg₂ List.cons (Lax560851.StructuralPresentation.Raw.nat.inj fields.1)
        (list_injective xs ys fields.2)

/-- The standard structural-list representation of a weighted graph. -/
noncomputable def input : Presentation Instance :=
  presentationOf (fun x => listToRaw nat (encodeInstance x.graph x.weights))

/-- Distinct mathematical instances have distinct structural representations. -/
theorem input_faithful : input.Faithful :=
  fun _ _ h => encodeInstance_injective (list_injective _ _ h)

/-- A solution is written as its membership vector. -/
def output (s : Solution) : List ℕ := encodeOutput s.2

/-- The vector's length and entries determine its ambient set and vertices. -/
theorem output_injective : Function.Injective output :=
  fun ⟨n,_I⟩ ⟨m,J⟩ h =>
    let order : n = m := List.length_ofFn.symm.trans
      ((congrArg List.length h).trans List.length_ofFn)
    match m, order, J, h with
    | _, rfl, _J, h =>
      congrArg (Sigma.mk n) (Finset.ext (fun v => flag_injective _ _
        (congrFun (List.ofFn_injective h) v)))

end Lax263307.IndependentSetEncoding
end

-- Lax263307.MaxWeightIndependentSet
section
namespace Lax263307

open GraphClasses WeightedIndependentSet

open Lax213208.OptimizationProblem

namespace MaxWeightIndependentSet

/-- A feasible solution is an independent set of the instance graph. -/
def IsFeasible (x : Instance) (s : Solution) : Prop :=
  ∃ I : Finset (Fin x.order), s = ⟨x.order, I⟩ ∧
    x.graph.IsIndepSet (I : Set (Fin x.order))

/-- Total weight, clipped at zero to meet the nonnegative-objective convention. -/
def objectiveValue (x : Instance) (s : Solution) : NNReal :=
  if h : s.1 = x.order then
    Real.toNNReal (weight x.weights (h ▸ s.2))
  else 0

/-- Weighted graphs whose underlying graph belongs to the given class. -/
def instancesOn (C : GraphClass) : Set Instance :=
  {x | x.graph ∈ C x.order}

end MaxWeightIndependentSet

/-- The mathematical optimization problem with its fixed canonical representations. -/
noncomputable def MaxWeightIndependentSet : Problem Instance Solution where
  direction := .maximize
  feasible := MaxWeightIndependentSet.IsFeasible
  value := MaxWeightIndependentSet.objectiveValue
  input := IndependentSetEncoding.input
  output := IndependentSetEncoding.output
  input_faithful := IndependentSetEncoding.input_faithful
  output_injective := IndependentSetEncoding.output_injective

end Lax263307
end

-- Lax263307.MainTheorem
section
namespace Lax263307.MainTheorem

open GraphClasses EdgeSublinearSeparators MaxWeightIndependentSet

open Lax213208.QPTAS (QPTAS)

/-- Theorem 2: the deterministic weighted approximation scheme. -/
axiom exists_qptas (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ alg, QPTAS (problem := MaxWeightIndependentSet) alg (instancesOn C)

end Lax263307.MainTheorem
end
