-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.Partrec
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.DeriveFintype

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

-- Lax496464.WH_A1_FptTime
section
namespace Lax496464.WH_A1_FptTime

open Lax808846.Ram Lax759944.BinaryWordEncoding Lax759944.RamPolytime

/-- The fixed-parameter bound `f(k) · (n + 1)^d`, for a parameter value `k` and an input size `n`. -/
def fptBound (f : ℕ → ℕ) (d k n : ℕ) : ℕ := f k * (n + 1) ^ d

/-- On every word `x` of `D`, the program `p` computes `F x` from the tape `x.length :: x`
within `B = f(κ x) · (bitSize x + 1)^d` instructions, at every word length `w ≥ B`; and the
tape and the output fit in words of length `B`. -/
def ComputesInFptTime (p : Program) (D : Set (List ℕ)) (κ : List ℕ → ℕ)
    (F : List ℕ → List ℕ) (f : ℕ → ℕ) (d : ℕ) : Prop :=
  ∀ x ∈ D,
    FitsInWords (fptBound f d (κ x) (bitSize x)) ((x.length :: x) ++ F x) ∧
      ∀ w : ℕ, fptBound f d (κ x) (bitSize x) ≤ w →
        ∃ t ≤ fptBound f d (κ x) (bitSize x), RunsTo w p (x.length :: x) (F x) t

/-- **Fixed-parameter time.** `F` is computable on the words of `D` in time `f(κ x) · (|x| + 1)^d`
by one program, for a computable `f` and a constant `d`. -/
def FptTimeOn (D : Set (List ℕ)) (κ : List ℕ → ℕ) (F : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (f : ℕ → ℕ) (d : ℕ), Computable f ∧ ComputesInFptTime p D κ F f d

end Lax496464.WH_A1_FptTime
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

-- Lax888481.ParameterizedComplexity
section
namespace Lax888481.ParameterizedComplexity

open Lax808846.Ram Lax808846.RamComputes

/-- A parameterized problem: the words that encode an instance, which of them are
yes-instances, and the parameter each one carries. -/
structure Problem where
  /-- The words that encode an instance. A program may do anything on the others. -/
  Domain : Set (List ℕ)
  /-- The yes-instances. -/
  Yes : List ℕ → Prop
  /-- The parameter, read off the word. -/
  param : List ℕ → ℕ

/-- The word `x` fits at word length `w`, with room for `c` times its length: every
entry `v` of `x` satisfies `c * (x.length + v + 1) ≤ 2 ^ w`. -/
def Fits (c w : ℕ) (x : List ℕ) : Prop := ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w

/-- The map `f` is an fpt-reduction from `P` to `Q`, computed by `prog` within
`c * g k * (|x| + 1)` instructions and raising the parameter by at most `h`. -/
structure IsFptReduction (P Q : Problem) (f : List ℕ → List ℕ) (prog : Program)
    (c : ℕ) (g h : ℕ → ℕ) : Prop where
  /-- The image of an admissible word is admissible. -/
  maps_domain : ∀ x ∈ P.Domain, f x ∈ Q.Domain
  /-- Yes-instances go to yes-instances, and no-instances to no-instances. -/
  correct : ∀ x ∈ P.Domain, (P.Yes x ↔ Q.Yes (f x))
  /-- The new parameter is bounded by a function of the old one alone. -/
  param_le : ∀ x ∈ P.Domain, Q.param (f x) ≤ h (P.param x)
  /-- At every word length, the program computes `f` on every admissible word that fits
  and whose image fits, within the stated bound. -/
  time : ∀ w : ℕ, ComputesInTime w prog
    {x | x ∈ P.Domain ∧ Fits c w x ∧ Fits c w (f x)}
    f (fun x => c * g (P.param x) * (x.length + 1))

/-- `P` **fpt-reduces** to `Q`. -/
def FptReduces (P Q : Problem) : Prop :=
  ∃ (f : List ℕ → List ℕ) (prog : Program) (c : ℕ) (g h : ℕ → ℕ),
    IsFptReduction P Q f prog c g h

@[inherit_doc] infix:50 " ≤fpt " => FptReduces

end Lax888481.ParameterizedComplexity
end

-- Lax496464.WH_A2_FptReductions
section
namespace Lax496464.WH_A2_FptReductions

open Lax888481.ParameterizedComplexity (Problem)

open Lax496464.WH_A1_FptTime

/-- **Step 1 of a reduction: construction and correctness.** `R` maps instances of `P` to
instances of `Q`, yes-instances to yes-instances and no-instances to no-instances. -/
structure IsReduction (P Q : Problem) (R : List ℕ → List ℕ) : Prop where
  /-- Instances go to instances. -/
  maps_domain : ∀ x ∈ P.Domain, R x ∈ Q.Domain
  /-- Yes-instances go to yes-instances, and no-instances to no-instances. -/
  correct : ∀ x ∈ P.Domain, (P.Yes x ↔ Q.Yes (R x))

/-- **Step 2 of a reduction: the parameter bound.** The parameter of `R x` is at most a computable
function of the parameter of `x`. -/
def ParamBounded (P Q : Problem) (R : List ℕ → List ℕ) : Prop :=
  ∃ g : ℕ → ℕ, Computable g ∧ ∀ x ∈ P.Domain, Q.param (R x) ≤ g (P.param x)

/-- An **fpt-reduction** [FG06, Definition 2.1]: a reduction with a bounded parameter,
computable in fixed-parameter time (**step 3**) on the instances of `P`. -/
structure IsFptReduction (P Q : Problem) (R : List ℕ → List ℕ) : Prop where
  /-- Construction and correctness. -/
  reduction : IsReduction P Q R
  /-- The parameter bound. -/
  param_bounded : ParamBounded P Q R
  /-- The running time. -/
  fpt_time : FptTimeOn P.Domain P.param R

/-- `P` **fpt-reduces** to `Q`. -/
def FptReduces (P Q : Problem) : Prop := ∃ R, IsFptReduction P Q R

@[inherit_doc] scoped infix:50 " ≤ᶠᵖᵗ " => FptReduces

end Lax496464.WH_A2_FptReductions
end

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax762056.GraphEncoding
section
namespace Lax762056.GraphEncoding

open List Turing Lax434930.PolynomialTime

structure Instance where
  order : ℕ
  graph : SimpleGraph (Fin order)
  threshold : ℕ

def unary (n : ℕ) : Word := replicate n true ++ [false]

noncomputable def encode (I : Instance) : Word := by
  classical
  exact unary I.order ++
    (finRange I.order).flatMap (fun u =>
      (finRange I.order).map (fun v => decide (I.graph.Adj u v))) ++
    unary I.threshold

end Lax762056.GraphEncoding
end

-- Lax762056.MaxCut
section
namespace Lax762056.MaxCut
end Lax762056.MaxCut
end

-- Lax762056.GraphProblems
section
namespace Lax762056.GraphProblems

open GraphEncoding MaxCut Turing

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

def IndependentSet (I : Instance) : Prop := I.threshold ≤ I.graph.indepNum

end Lax762056.GraphProblems
end

-- Lax496464.WH_F1_IndependentSetMatrix
section
namespace Lax496464.WH_F1_IndependentSetMatrix

open Lax762056.GraphEncoding Lax888481.ParameterizedComplexity

/-- A bit as a number. -/
def bitNat (b : Bool) : ℕ := if b then 1 else 0

/-- The word of an instance: its adjacency-matrix encoding, one number `0` or `1` per bit. -/
noncomputable def word (I : Instance) : List ℕ := (encode I).map bitNat

/-- The words that present an instance. -/
def Instances : Set (List ℕ) := Set.range word

/-- The parameter `k` of a word: the run of ones ending just before its last entry. -/
def threshold (x : List ℕ) : ℕ := (x.dropLast.reverse.takeWhile fun v => v == 1).length

/-- **`p-Independent-Set`** on adjacency-matrix words. -/
def problem : Problem where
  Domain := Instances
  Yes x := ∃ I, x = word I ∧ Lax762056.GraphProblems.IndependentSet I
  param := threshold

end Lax496464.WH_F1_IndependentSetMatrix
end

-- Lax271696.GraphEncoding
section
namespace Lax271696.GraphEncoding

/-- The number of vertices declared by a word: its first entry. -/
def vertexCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of edges declared by a word: its second entry. -/
def edgeCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The `i`-th offset of a word: the `n+1` offsets follow the two
header entries. -/
def offset (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + i) 0

/-- The `j`-th entry of the target array of a word, which follows the
header and the offsets. -/
def target (x : List ℕ) (j : ℕ) : ℕ := x.getD (3 + vertexCount x + j) 0

/-- The word `x` is a compressed sparse row encoding of the graph `G`
on `n` vertices. -/
structure EncodesGraph (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) :
    Prop where
  /-- The word declares `n` vertices. -/
  vertexCount_eq : vertexCount x = n
  /-- The word consists of the two header entries, the `n+1` offsets,
  and a target array of length twice the declared number of edges. -/
  length_eq : x.length = 3 + n + 2 * edgeCount x
  /-- The block of the first vertex begins at the start of the target
  array. -/
  offset_zero : offset x 0 = 0
  /-- The block of the last vertex ends at the end of the target
  array. -/
  offset_last : offset x n = 2 * edgeCount x
  /-- The offsets are nondecreasing, so they cut the target array into
  one block per vertex. -/
  offset_mono : ∀ i < n, offset x i ≤ offset x (i + 1)
  /-- Every entry of the target array is a vertex. -/
  target_lt : ∀ j < 2 * edgeCount x, target x j < n
  /-- The block of a vertex lists exactly its neighbors. -/
  adj_iff : ∀ u v : Fin n, G.Adj u v ↔
    ∃ j, offset x u ≤ j ∧ j < offset x (u + 1) ∧ target x j = v

end Lax271696.GraphEncoding
end

-- Lax888481.MulticolouredClique
section
namespace Lax888481.MulticolouredClique

/-- An instance of Multicoloured Clique: a graph whose vertices are coloured so that
adjacent vertices differ in colour. -/
structure Instance where
  /-- The number `k` of colours, the parameter. -/
  colours : ℕ
  /-- The number `n` of vertices. -/
  vertices : ℕ
  /-- The graph. -/
  graph : SimpleGraph (Fin vertices)
  /-- The colour of each vertex. -/
  colour : Fin vertices → Fin colours
  /-- Adjacent vertices differ in colour. -/
  adj_colour_ne : ∀ u v, graph.Adj u v → colour u ≠ colour v

/-- `G` contains a multicoloured clique: one vertex of each colour, pairwise adjacent. -/
def Instance.HasMulticolouredClique (G : Instance) : Prop :=
  ∃ f : Fin G.colours → Fin G.vertices,
    (∀ c, G.colour (f c) = c) ∧ ∀ c c', c ≠ c' → G.graph.Adj (f c) (f c')

/-- The word `x` presents the instance `G`: a compressed sparse row block encoding the
graph, with each adjacency list strictly increasing, followed by one entry per vertex
giving its colour, followed by the number of colours. -/
def EncodesInstance (x : List ℕ) (G : Instance) : Prop :=
  ∃ g, x = g ++ (List.ofFn fun v => (G.colour v : ℕ)) ++ [G.colours] ∧
    Lax271696.GraphEncoding.EncodesGraph g G.vertices G.graph ∧
    ∀ u < G.vertices, ∀ t, Lax271696.GraphEncoding.offset g u ≤ t →
      t + 1 < Lax271696.GraphEncoding.offset g (u + 1) →
      Lax271696.GraphEncoding.target g t < Lax271696.GraphEncoding.target g (t + 1)

/-- The words that encode an instance. -/
def Instances : Set (List ℕ) := {x | ∃ G, EncodesInstance x G}

/-- **Multicoloured Clique**, parameterized by the number of colours. The parameter is
the last entry of the word. -/
def problem : ParameterizedComplexity.Problem where
  Domain := Instances
  Yes x := ∃ G, EncodesInstance x G ∧ G.HasMulticolouredClique
  param x := x.getLast? |>.getD 0

end Lax888481.MulticolouredClique
end

-- Lax496464.WH_F2_MccConstruction
section
namespace Lax496464.WH_F2_MccConstruction.graph
end Lax496464.WH_F2_MccConstruction.graph

namespace Lax496464.WH_F2_MccConstruction

open Lax762056.GraphEncoding (Instance)

open Classical in
/-- Adjacency in `G` of the numbers `u` and `v`; false unless both are vertices. -/
noncomputable def adjG (I : Instance) (u v : ℕ) : Bool :=
  decide (∃ (hu : u < I.order) (hv : v < I.order), I.graph.Adj ⟨u, hu⟩ ⟨v, hv⟩)

/-- The number `k · n` of vertices of the multicoloured graph. -/
def size (I : Instance) : ℕ := I.threshold * I.order

/-- Adjacency in the multicoloured graph of the numbers `s` and `t`; false unless both are
vertices. -/
noncomputable def adjB (I : Instance) (s t : ℕ) : Bool :=
  decide (s < size I ∧ t < size I ∧ s / I.order ≠ t / I.order ∧ s % I.order ≠ t % I.order ∧
    adjG I (s % I.order) (t % I.order) = false)

/-- The neighbours of the vertex `s`, in increasing order. -/
noncomputable def neighbours (I : Instance) (s : ℕ) : List ℕ :=
  (List.range (size I)).filter (adjB I s)

/-- The target array: the neighbours of each vertex in turn. -/
noncomputable def targets (I : Instance) : List ℕ :=
  (List.range (size I)).flatMap (neighbours I)

/-- The offsets: `0`, then the running sums of the degrees. -/
noncomputable def offsets (I : Instance) : List ℕ :=
  (List.range (size I + 1)).map fun s => ((List.range s).map fun r => (neighbours I r).length).sum

/-- The colour of each vertex. -/
def colours (I : Instance) : List ℕ := (List.range (size I)).map fun s => s / I.order

/-- **The word of the multicoloured graph**: the number of vertices, the number of edges, the
offsets, the targets, the colours, and the number of colours. -/
noncomputable def word (I : Instance) : List ℕ :=
  [size I, (targets I).length / 2] ++ offsets I ++ targets I ++ colours I ++ [I.threshold]

open Classical in
/-- **The reduction**: the word of the multicoloured graph on the word of an instance, and the
empty word elsewhere. -/
noncomputable def reduce (x : List ℕ) : List ℕ :=
  if h : x ∈ WH_F1_IndependentSetMatrix.Instances then word (Classical.choose h) else []

end Lax496464.WH_F2_MccConstruction
end

-- Lax888481.PolynomialReduction
section
namespace Lax888481
end Lax888481

namespace Lax888481.PolynomialReduction
end Lax888481.PolynomialReduction
end

-- Lax496464.WH_F4_IndependentSetToMcc
section
namespace Lax496464.WH_F4_IndependentSetToMcc

open Lax762056.GraphEncoding (Instance)

section Words

open Lax496464.WH_F1_IndependentSetMatrix (problem)

open Lax496464.WH_F2_MccConstruction (reduce)

end Words

section Time

open Lax808846.Ram Lax808846.RamComputes Lax888481.ParameterizedComplexity

open Lax496464.WH_F1_IndependentSetMatrix (problem)

open Lax496464.WH_F2_MccConstruction (reduce)

/-- **Independent Set strictly fpt-reduces to Multicoloured Clique.** -/
axiom independentSet_fptReduces_mcc :
    Lax888481.ParameterizedComplexity.FptReduces problem Lax888481.MulticolouredClique.problem

end Time

section Library

open Lax496464.WH_A2_FptReductions

end Library

end Lax496464.WH_F4_IndependentSetToMcc
end
