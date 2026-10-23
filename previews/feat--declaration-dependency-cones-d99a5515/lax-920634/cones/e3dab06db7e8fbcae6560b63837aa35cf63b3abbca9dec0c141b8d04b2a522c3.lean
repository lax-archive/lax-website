-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic

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

-- Lax808846.RamComputes
section
namespace Lax808846.RamComputes
end Lax808846.RamComputes
end

-- Lax920634.EdgeExpansion
section
namespace Lax920634
end Lax920634

namespace Lax920634.EdgeExpansion
end Lax920634.EdgeExpansion
end

-- Lax920634.SeedSearch
section
namespace Lax920634.SeedSearch

open Function

/-- A table of thirty maps on a numbered finite vertex set. -/
abbrev Table (n : ℕ) := Fin 30 → Fin n → Fin n

/-- The number of vertices of `S` whose image lies outside `S`. -/
def escape {n : ℕ} (f : Fin n → Fin n) (S : Finset (Fin n)) : ℕ :=
  (S.filter fun v => f v ∉ S).card

/-- Each row is a permutation, and some row moves at least a tenth of each small set out. -/
abbrev GoodTable {n : ℕ} (T : Table n) : Prop :=
  (∀ i, Bijective (T i)) ∧
    ∀ S : Finset (Fin n), 2 * S.card ≤ n →
      ∃ i : Fin 30, S.card ≤ 10 * escape (T i) S

/-- The candidate table represented by a base-`n` integer. -/
def decode (n : ℕ) (code : Fin (n ^ (30 * n))) : Table n :=
  fun i v => finFunctionFinEquiv.symm code (finProdFinEquiv (i, v))

/-- All candidate codes in increasing numerical order. -/
def candidates (n : ℕ) : List (Fin (n ^ (30 * n))) := List.finRange _

/-- The first expanding permutation table found by the finite deterministic scan. -/
def selectedTable (n : ℕ) : Table n :=
  (((candidates n).find? fun code => decide (GoodTable (decode n code))).map
    (decode n)).getD (fun _ v => v)

/-- Find the inverse image by scanning a numbered finite vertex set. -/
def inverse {n : ℕ} (f : Fin n → Fin n) (v : Fin n) : Fin n :=
  ((List.finRange n).find? fun u => decide (f u = v)).getD v

/-- A fixed powering exponent sufficient for the lazy permutation seed. -/
def poweringExponent : ℕ := 5760000

/-- The fixed degree of the powered seed. -/
def seedDegree : ℕ := 120 ^ poweringExponent

/-- The fixed number of seed vertices, the fourth power of its degree. -/
def seedOrder : ℕ := seedDegree ^ 4

end Lax920634.SeedSearch
end

-- Lax920634.SeedRotation
section
namespace Lax920634.SeedRotation

open SeedSearch

/-- Number forward and inverse permutation darts by integers below sixty. -/
def permutationLabels : (Fin 30 × Bool) ≃ Fin 60 :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv

/-- Number the permutation darts and the sixty stationary darts together. -/
def lazyLabels : ((Fin 30 × Bool) ⊕ Fin 60) ≃ Fin 120 :=
  (Equiv.sumCongr permutationLabels (Equiv.refl _)).trans finSumFinEquiv

/-- The rotation of the selected lazy permutation graph, with numbered labels. -/
def lazyRotation (n : ℕ) (p : Fin n × Fin 120) : Fin n × Fin 120 :=
  match lazyLabels.symm p.2 with
  | Sum.inl (i, false) =>
    (selectedTable n i p.1, lazyLabels (Sum.inl (i, true)))
  | Sum.inl (i, true) =>
    (inverse (selectedTable n i) p.1,
      lazyLabels (Sum.inl (i, false)))
  | Sum.inr j => (p.1, lazyLabels (Sum.inr j))

/-- Follow a finite sequence of numbered darts to its endpoint. -/
def walkEnd {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d) :
    (t : ℕ) → Fin n → (Fin t → Fin d) → Fin n
  | 0, v, _ => v
  | t + 1, v, s => walkEnd R t (R (v, s 0)).1 (fun j => s j.succ)

/-- The vertex reached after a prescribed number of steps of a finite dart sequence. -/
def walkAt {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (t : ℕ) (v : Fin n) (s : Fin t → Fin d) : ℕ → Fin n
  | 0 => v
  | k + 1 => if h : k < t then
    (R (walkAt R t v s k, s ⟨k, h⟩)).1 else walkAt R t v s k

/-- The edge rotation of a graph power, with dart sequences numbered in base `d`. -/
def powerRotation {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (t : ℕ) (p : Fin n × Fin (d ^ t)) : Fin n × Fin (d ^ t) :=
  let s := finFunctionFinEquiv.symm p.2
  (walkEnd R t p.1 s, finFunctionFinEquiv (fun j =>
    (R (walkAt R t p.1 s (Fin.rev j).val, s (Fin.rev j))).2))

/-- The fixed seed's rotation map, after lazy powering. -/
def rotation : Fin seedOrder × Fin seedDegree →
    Fin seedOrder × Fin seedDegree :=
  powerRotation (lazyRotation seedOrder) poweringExponent

end Lax920634.SeedRotation
end

-- Lax920634.ZigZagConstruction
section
namespace Lax920634.ZigZagConstruction

open SeedSearch

/-- The fixed degree of each regular graph in the tower. -/
def degree : ℕ := seedDegree ^ 2

/-- The number of vertices in the regular graph at a given level. -/
def baseOrder (k : ℕ) : ℕ := (seedDegree ^ 4) ^ (k + 1)

/-- The number of vertices after path replacement at a given level. -/
def order (k : ℕ) : ℕ := baseOrder k * degree

/-- A total numerical query to the fixed seed's edge rotation. -/
def seedValue (p : ℕ × ℕ) : ℕ × ℕ :=
  if h : p.1 < seedOrder ∧ p.2 < seedDegree then
    let r := SeedRotation.rotation (⟨p.1, h.1⟩, ⟨p.2, h.2⟩)
    (r.1.val, r.2.val)
  else (0, 0)

/-- The regular tower's rotation, computed by squaring and zig-zag steps. -/
def rotation : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, (v, i) =>
      let p₀ := seedValue (v, i / seedDegree)
      let p₁ := seedValue (p₀.1, i % seedDegree)
      (p₁.1, p₀.2 + seedDegree * p₁.2)
  | k + 1, (v, i) =>
      let p := seedValue (v % seedDegree ^ 4, i / seedDegree)
      let q₀ := rotation k (v / seedDegree ^ 4, p.1 / degree)
      let q₁ := rotation k (q₀.1, p.1 % degree)
      let r := seedValue (q₀.2 + degree * q₁.2, i % seedDegree)
      (r.1 + seedDegree ^ 4 * q₁.1, p.2 + seedDegree * r.2)

/-- The matching endpoint of a port, in the canonical vertex numbering. -/
def matchingNeighbor (k v : ℕ) : ℕ :=
  let r := rotation k (v / degree, v % degree)
  r.2 + degree * r.1

end Lax920634.ZigZagConstruction
end

-- Lax920634.GraphEncoding
section
namespace Lax920634.GraphEncoding

open SeedSearch ZigZagConstruction

/-- The bounded level-selection loop, carrying the level and current regular order. -/
def levelAfter (b n : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | j + 1, p =>
      let q := levelAfter b n j p
      if q.2 < 2 * n then (q.1 + 1, q.2 * b) else q

/-- The level selected for a requested order, after at most `2*n` advances. -/
def selectedLevel (n : ℕ) : ℕ :=
  (levelAfter (seedDegree ^ 4) n (2 * n) (0, seedDegree ^ 4)).1

end Lax920634.GraphEncoding
end

-- Lax920634.WordEncoding
section
namespace Lax920634.WordEncoding

open ZigZagConstruction GraphEncoding

/-- The complete matching table, with its graph order as a header. -/
def table (k : ℕ) : List ℕ := order k ::
  (List.range (order k)).map (matchingNeighbor k)

/-- Construct the word encoding for the same size selector as the binary constructor. -/
def construct (n : ℕ) : List ℕ := table (selectedLevel n)

end Lax920634.WordEncoding
end

-- Lax920634.LinearConstruction
section
namespace Lax920634.LinearConstruction

open ZigZagConstruction Lax808846.Ram

open GraphEncoding (selectedLevel)

open WordEncoding (construct)

/-- A uniform deterministic RAM constructs the precise family in linear output time. -/
axiom linear_time : ∃ (program : Program) (timeConstant wordConstant : ℕ),
  0 < timeConstant ∧ 0 < wordConstant ∧
  ∀ (n w : ℕ),
    wordConstant * (order (selectedLevel n) + 1) ≤ 2 ^ w →
    ∃ t ≤ timeConstant * (order (selectedLevel n) + 1),
      RunsTo w program [n] (construct n) t

end Lax920634.LinearConstruction
end
