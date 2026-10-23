-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sublists
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.DeriveFintype

-- Lax263307.LinearRelaxation
section
namespace Lax263307.LinearRelaxation.IsFeasible
end Lax263307.LinearRelaxation.IsFeasible

namespace Lax263307.LinearRelaxation

/-- The coordinate sets of the level-`r` relaxation. -/
abbrev Coordinate (n r : ℕ) := {A : Finset (Fin n) // A.card ≤ r + 2}

/-- A vector with precisely the coordinates used by the relaxation. -/
abbrev MomentVector (n r : ℕ) := Coordinate n r → ℝ

end Lax263307.LinearRelaxation
end

-- Lax263307.ConditionedCosts
section
namespace Lax263307.ConditionedCosts
end Lax263307.ConditionedCosts
end

-- Lax263307.ConditioningDistribution
section
namespace Lax263307.ConditioningDistribution
end Lax263307.ConditioningDistribution
end

-- Lax263307.Entropy
section
namespace Lax263307
end Lax263307

namespace Lax263307.Entropy
end Lax263307.Entropy
end

-- Lax263307.EntropyBounds
section
namespace Lax263307.EntropyBounds
end Lax263307.EntropyBounds
end

-- Lax263307.EntropyGap
section
namespace Lax263307.EntropyGap
end Lax263307.EntropyGap
end

-- Lax263307.HeavyConditioning
section
namespace Lax263307.HeavyConditioning

open LinearRelaxation ConditioningDistribution Entropy

noncomputable def probabilityFloor (n p : ℕ) : ℝ :=
  1 / (2 * (n : ℝ) * p * ((Nat.log2 n : ℝ) + 1))

end Lax263307.HeavyConditioning
end

-- Lax109476.LinearProgram
section
open scoped BigOperators

namespace Lax109476.LinearProgram

/-- Coefficients of a maximization program with `m` inequalities and `n`
nonnegative variables. -/
structure Program (K : Type) (m n : ℕ) where
  /-- The constraint matrix. -/
  A : Fin m → Fin n → K
  /-- The upper bounds on the constraint rows. -/
  b : Fin m → K
  /-- The coefficients of the maximized objective. -/
  c : Fin n → K

/-- The dual objective value. -/
def dualValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (y : Fin m → K) : K :=
  ∑ i, P.b i * y i

end Lax109476.LinearProgram
end

-- Lax109476.FarkasCertificate
section
namespace Lax109476.FarkasCertificate
end Lax109476.FarkasCertificate
end

-- Lax109476.RecessionDirection
section
namespace Lax109476.RecessionDirection
end Lax109476.RecessionDirection
end

-- Lax109476.RationalCertificates
section
namespace Lax109476.RationalCertificates.IsValidCertificate
end Lax109476.RationalCertificates.IsValidCertificate

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

/-- A rational certificate for one of the three possible LP outcomes. -/
inductive Certificate (m n : ℕ)
  /-- Primal and dual points with matching objectives. -/
  | optimal (x : Fin n → ℚ) (y : Fin m → ℚ)
  /-- Separating nonnegative multipliers for an infeasible primal system. -/
  | infeasible (y : Fin m → ℚ)
  /-- A feasible base point and an improving recession direction. -/
  | unbounded (x d : Fin n → ℚ)

end Lax109476.RationalCertificates
end

-- Lax263307.ComponentCuts
section
namespace Lax263307.ComponentCuts
end Lax263307.ComponentCuts
end

-- Lax263307.ComponentCutEncoding
section
namespace Lax263307.ComponentCutEncoding

open LinearRelaxation

/-- The coefficient at one coordinate, after collecting all repeated terms. -/
def coefficient {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (B : Coordinate n r) : ℤ :=
  (∑ v ∈ C, if insert v A = B.val then 1 else 0) -
    if A = B.val then (u : ℤ) else 0

/-- Evaluate the coefficient vector in the real coordinate space. -/
noncomputable def evaluate {n r : ℕ} (a : Coordinate n r → ℤ)
    (z : MomentVector n r) : ℝ := ∑ B, (a B : ℝ) * z B

end Lax263307.ComponentCutEncoding
end

-- Lax263307.RationalConditioning
section
namespace Lax263307.RationalConditioning

open LinearRelaxation Entropy

/-- Rational coordinates for the same truncated relaxation. -/
abbrev RationalVector (n r : ℕ) := Coordinate n r → ℚ

/-- Read a rational coordinate, extending by zero outside the coordinate domain. -/
def rationalValue {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n)) : ℚ :=
  if h : A.card ≤ r + 2 then y ⟨A, h⟩ else 0

/-- The ordered edge-product numerator in the exact test. -/
def edgeNumerator {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) : ℚ :=
  ∑ u, ∑ v, if G.Adj u v then
    rationalValue y (insert u A) * rationalValue y (insert v A) else 0

/-- The exact rational test after clearing the positive conditioning denominator. -/
def Passes {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Prop :=
  0 < rationalValue y A ∧
    (p : ℚ) * edgeNumerator G y A ≤ 2 * (k : ℚ) ^ 2 * rationalValue y A ^ 2

/-- The rational test is decidable by exact arithmetic. -/
instance {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Decidable (Passes G k p y A) :=
  inferInstanceAs (Decidable (0 < rationalValue y A ∧
    (p : ℚ) * edgeNumerator G y A ≤ 2 * (k : ℚ) ^ 2 * rationalValue y A ^ 2))

/-- Enumerate only sublists with lengths between zero and the conditioning budget. -/
def candidates (n r : ℕ) : List (Finset (Fin n)) :=
  (List.range (r + 1)).flatMap fun j =>
    ((List.finRange n).sublistsLen j).map List.toFinset

end Lax263307.RationalConditioning
end

-- Lax263307.CoordinateCatalog
section
namespace Lax263307.CoordinateCatalog

open LinearRelaxation RationalConditioning

private theorem mem_candidates (n r : ℕ) (A : Finset (Fin n)) :
    A ∈ candidates n r ↔ A.card ≤ r :=
  ⟨fun member =>
    let ⟨j, inRange, inSublists⟩ := List.mem_flatMap.mp member
    let ⟨vertices, listed, sameSet⟩ := List.mem_map.mp inSublists
    let sublist := (List.mem_sublistsLen.mp listed).1
    let length := (List.mem_sublistsLen.mp listed).2
    calc
      A.card = vertices.toFinset.card := congrArg Finset.card sameSet.symm
      _ = vertices.length := List.toFinset_card_of_nodup (sublist.nodup (List.nodup_finRange n))
      _ = j := length
      _ ≤ r := Nat.le_of_lt_succ (List.mem_range.mp inRange),
   fun bounded =>
    let vertices := (List.finRange n).filter fun v => decide (v ∈ A)
    let sublist : vertices.Sublist (List.finRange n) := List.filter_sublist
    let sameSet : vertices.toFinset = A := Finset.ext fun v =>
      List.mem_toFinset.trans (List.mem_filter.trans
        ⟨fun h => of_decide_eq_true h.2,
         fun h => ⟨List.mem_finRange v, decide_eq_true h⟩⟩)
    let length : vertices.length = A.card :=
      (List.toFinset_card_of_nodup (sublist.nodup (List.nodup_finRange n))).symm.trans
        (congrArg Finset.card sameSet)
    List.mem_flatMap.mpr ⟨A.card, List.mem_range.mpr (Nat.lt_succ_of_le bounded),
      List.mem_map.mpr ⟨vertices, List.mem_sublistsLen.mpr ⟨sublist, length⟩, sameSet⟩⟩⟩

def sets (n r : ℕ) : List (Finset (Fin n)) := (candidates n (r + 2)).dedup

def catalog (n r : ℕ) : List (Coordinate n r) :=
  (sets n r).attach.map (fun A => ⟨A.val,
    (mem_candidates n (r + 2) A.val).mp
      (List.mem_dedup.mp A.property)⟩)

private theorem mem_catalog (n r : ℕ) (A : Coordinate n r) : A ∈ catalog n r :=
  let listed : A.val ∈ sets n r :=
    List.mem_dedup.mpr ((mem_candidates n (r + 2) A.val).mpr A.property)
  List.mem_map.mpr ⟨⟨A.val, listed⟩, List.mem_attach _ _, Subtype.ext rfl⟩

private theorem catalog_nodup (n r : ℕ) : (catalog n r).Nodup :=
  (List.nodup_dedup _).attach.map fun _ _ equal =>
    Subtype.ext (congrArg (fun coordinate : Coordinate n r => coordinate.val) equal)

def indexing (n r : ℕ) : Fin (catalog n r).length ≃ Coordinate n r :=
  List.Nodup.getEquivOfForallMemList (catalog n r) (catalog_nodup n r) (mem_catalog n r)

end Lax263307.CoordinateCatalog
end

-- Lax263307.MomentLP
section
namespace Lax263307.MomentLP

open ComponentCutEncoding (evaluate)

open LinearRelaxation CoordinateCatalog

open Lax109476.LinearProgram Lax109476.RationalCertificates

abbrev dimension (n r : ℕ) : ℕ := (catalog n r).length

abbrev Index (n r : ℕ) := Fin (dimension n r)

/-- Row blocks for normalization, coordinate bounds, independence, monotonicity, and mass. -/
abbrev rowCount (n r : ℕ) : ℕ :=
  let N := dimension n r
  2 + (N + (N + (N * n + (N + N))))

def decode {K : Type} {n r : ℕ} (x : Index n r → K) : Coordinate n r → K :=
  fun A => x ((indexing n r).symm A)

def encode {K : Type} {n r : ℕ} (y : Coordinate n r → K) : Index n r → K :=
  fun j => y (indexing n r j)

def singleRow {n r : ℕ} (A : Finset (Fin n)) (j : Index n r) : ℚ :=
  if A = (indexing n r j).val then 1 else 0

def monotoneRow {n r : ℕ} (A : Finset (Fin n)) (v : Fin n) (j : Index n r) : ℚ :=
  singleRow (insert v A) j - singleRow A j

def massRow {n r : ℕ} (A : Finset (Fin n)) (k : ℕ) (j : Index n r) : ℚ :=
  (∑ v, singleRow (insert v A) j) - (k : ℚ) * singleRow A j

def program {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    Program ℚ (rowCount n r) (dimension n r) where
  A := Fin.addCases
    (fun i : Fin 2 => fun j => if i = 0 then singleRow ∅ j else -singleRow ∅ j)
    (Fin.addCases
      (fun i : Index n r => singleRow (indexing n r i).val)
      (Fin.addCases
        (fun i : Index n r => fun j =>
          if G.IsIndepSet ((indexing n r i).val : Set (Fin n)) then 0 else singleRow (indexing n r i).val j)
        (Fin.addCases
          (fun i : Fin (dimension n r * n) =>
            let uv := finProdFinEquiv.symm i
            if (indexing n r uv.1).val.card ≤ r + 1 then
              monotoneRow (indexing n r uv.1).val uv.2 else fun _ => 0)
          (Fin.addCases
            (fun i : Index n r =>
              if (indexing n r i).val.card ≤ r + 1 then massRow (indexing n r i).val k else fun _ => 0)
            (fun i : Index n r => fun j =>
              if (indexing n r i).val.card ≤ r + 1 then -massRow (indexing n r i).val k j else 0)))))
  b := Fin.addCases (fun i : Fin 2 => if i = 0 then 1 else -1)
    (Fin.addCases (fun _ : Index n r => 1) (fun _ => 0))
  c := fun _ => 0

end Lax263307.MomentLP
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

/-- Polynomial-time computation by one uniform word-RAM program, measured
in the bit-size of the logical word-list input. The physical input is explicitly
length-prefixed. All instructions of Lax808846 are available, including access
to the immutable original input independently of sequential reads. -/
def RamPolytime (f : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (wordBound timeBound : Polynomial ℕ),
    ∀ x : List ℕ,
      FitsInWords (wordBound.eval (bitSize x)) ((x.length :: x) ++ f x) ∧
        ∀ w : ℕ, wordBound.eval (bitSize x) ≤ w →
          ∃ t ≤ timeBound.eval (bitSize x),
            RunsTo w p (x.length :: x) (f x) t

end Lax759944.RamPolytime
end

-- Lax109476.RationalEncoding
section
namespace Lax109476.RationalEncoding.encodeCertificate
end Lax109476.RationalEncoding.encodeCertificate

namespace Lax109476.RationalEncoding

open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- Encode a reduced rational by sign, magnitude, and denominator. -/
def encodeRational (q : ℚ) : List ℕ :=
  [if q.num < 0 then 1 else 0, q.num.natAbs, q.den]

/-- Encode all coordinates of a rational vector in index order. -/
def encodeVector {n : ℕ} (x : Fin n → ℚ) : List ℕ :=
  (List.ofFn x).flatMap encodeRational

/-- Encode dimensions, row-major coefficients, row bounds, and objective. -/
def encodeProgram {m n : ℕ} (P : Program ℚ m n) : List ℕ :=
  [m, n] ++ (List.ofFn fun i => List.ofFn (P.A i)).flatten.flatMap encodeRational ++
    encodeVector P.b ++ encodeVector P.c

end Lax109476.RationalEncoding
end

-- Lax263307.BufferedEllipsoid
section
namespace Lax263307.BufferedEllipsoid

open Matrix

def scale {K : Type} [Field K] {n : ℕ} (z : Fin n → K) : Fin n → K := fun i => z i / (4 * (n : K))

end Lax263307.BufferedEllipsoid
end

-- Lax263307.RoundedOracleSearch
section
namespace Lax263307.RoundedOracleSearch.scan
end Lax263307.RoundedOracleSearch.scan

namespace Lax263307.RoundedOracleSearch.selectedNormal
end Lax263307.RoundedOracleSearch.selectedNormal

namespace Lax263307.RoundedOracleSearch.trajectory
end Lax263307.RoundedOracleSearch.trajectory

namespace Lax263307.RoundedOracleSearch

open BufferedEllipsoid (scale)

open Lax109476.RationalEncoding (encodeRational)

open Lax759944.BinaryWordEncoding (bitSize)

open Matrix

inductive Reply (n : ℕ) (Result : Type)
  | found (answer : Result)
  | reject
  | cut (normal : Fin n → ℤ)

def rationalNormal {n : ℕ} (a : Fin n → ℤ) : Fin n → ℚ := fun i => a i

def steps (n B : ℕ) : ℕ := 4 * (n + 1) * (B * n + 1)

end Lax263307.RoundedOracleSearch
end

-- Lax263307.AlgorithmParameters
section
namespace Lax263307.AlgorithmParameters

open HeavyConditioning (probabilityFloor)

open MomentLP (dimension)

open RoundedOracleSearch (steps)

def logarithm (n : ℕ) : ℕ := Nat.log2 (2 * n) + 1

def load (B n D : ℕ) : ℕ := 12 * B * D * logarithm n

def targetThreshold (a K B n D : ℕ) : ℕ := K * (load B n D + 1) ^ (4 * a + 2)

def sparsity (a K B n D : ℕ) : ℕ := 2 * targetThreshold a K B n D

def level (a K B n D : ℕ) : ℕ := sparsity a K B n D * (Nat.log2 n + 1)

def floorDenominator (a K B n D : ℕ) : ℕ :=
  2 * n * sparsity a K B n D * (Nat.log2 n + 1)

def momentFloor (a K B n D : ℕ) : ℚ :=
  1 / (floorDenominator a K B n D : ℚ) ^ level a K B n D

end Lax263307.AlgorithmParameters
end

-- Lax263307.SeparatorComponents
section
namespace Lax263307.SeparatorComponents

/-- A partition of the undeleted vertices, closed under undeleted edges. -/
structure Partition {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (ι : Type) where
  /-- The original vertices in each part. -/
  vertices : ι → Finset (Fin n)
  /-- Parts exclude the deleted vertices. -/
  outside : ∀ i v, v ∈ vertices i → v ∉ S
  /-- Every undeleted vertex belongs to exactly one part. -/
  unique : ∀ v, v ∉ S → ∃! i, v ∈ vertices i
  /-- No undeleted edge leaves a part. -/
  closed : ∀ i u v, u ∈ vertices i → v ∉ S → G.Adj u v → v ∈ vertices i

/-- The recursive answer is the union of the answers on the parts. -/
def combine {n : ℕ} {ι : Type} [Fintype ι] (I : ι → Finset (Fin n)) :
    Finset (Fin n) := Finset.univ.biUnion I

end Lax263307.SeparatorComponents
end

-- Lax263307.RecursiveRounding
section
namespace Lax263307.RecursiveRounding
end Lax263307.RecursiveRounding
end

-- Lax263307.StrongComponentGaps
section
namespace Lax263307.StrongComponentGaps
end Lax263307.StrongComponentGaps
end

-- Lax263307.HeavyRecursiveRounding
section
namespace Lax263307.HeavyRecursiveRounding
end Lax263307.HeavyRecursiveRounding
end

-- Lax263307.ComputedRounding
section
namespace Lax263307.ComputedRounding.collect_correct
end Lax263307.ComputedRounding.collect_correct

namespace Lax263307.ComputedRounding

open SeparatorComponents (combine)

def target (δ cost : ℚ) : ℕ := ⌊(1 - δ) * cost⌋₊ + 1

def answer {n : ℕ} {ι : Type} (δ : ℚ) (k : ℕ) (cost : ι → ℚ)
    (query : ι → ℕ → Option (Finset (Fin n))) (i : ι) : Option (Finset (Fin n)) :=
  if δ * k / (4 * n) < cost i then query i (target δ (cost i)) else some ∅

inductive Result (n : ℕ)
  | found (vertices : Finset (Fin n))
  | cut (vertices : Finset (Fin n)) (bound : ℕ)

def collect {n : ℕ} {ι : Type} [Fintype ι] (order : List ι) (parts : ι → Finset (Fin n))
    (δ : ℚ) (k : ℕ) (cost : ι → ℚ) (query : ι → ℕ → Option (Finset (Fin n))) : Result n :=
  match order.find? (fun i => (answer δ k cost query i).isNone) with
  | some i => .cut (parts i) (target δ (cost i) - 1)
  | none => .found (combine (fun i => (answer δ k cost query i).getD ∅))

open LinearRelaxation SeparatorComponents

open ComponentCutEncoding

end Lax263307.ComputedRounding
end

-- Lax263307.GraphClasses
section
namespace Lax263307
end Lax263307

namespace Lax263307.GraphClasses
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

end Lax263307.EdgeSublinearSeparators
end

-- Lax263307.BalancedPartitions
section
namespace Lax263307.BalancedPartitions
end Lax263307.BalancedPartitions
end

-- Lax263307.PathSampling
section
namespace Lax263307.PathSampling
end Lax263307.PathSampling

namespace Lax263307.PathSampling.Distribution
end Lax263307.PathSampling.Distribution
end

-- Lax263307.RepeatedCutAccounting
section
namespace Lax263307.RepeatedCutAccounting
end Lax263307.RepeatedCutAccounting
end

-- Lax263307.CutTraces
section
namespace Lax263307.CutTraces
end Lax263307.CutTraces

namespace Lax263307.CutTraces.Trace
end Lax263307.CutTraces.Trace

namespace Lax263307.CutTraces.parts
end Lax263307.CutTraces.parts
end

-- Lax228581.Treewidth
section
namespace Lax228581
end Lax228581

namespace Lax228581.Treewidth
end Lax228581.Treewidth

namespace Lax228581.Treewidth.TreeDecomposition
end Lax228581.Treewidth.TreeDecomposition
end

-- Lax263307.ConnectedBags
section
namespace Lax263307
end Lax263307

namespace Lax263307.ConnectedBags
end Lax263307.ConnectedBags
end

-- Lax263307.ConnectedRepresentations
section
namespace Lax263307.ConnectedRepresentations
end Lax263307.ConnectedRepresentations

namespace Lax263307.ConnectedRepresentations.Representation
end Lax263307.ConnectedRepresentations.Representation
end

-- Lax263307.AlmostEmbeddings
section
namespace Lax263307.AlmostEmbeddings
end Lax263307.AlmostEmbeddings

namespace Lax263307.AlmostEmbeddings.AlmostEmbedding
end Lax263307.AlmostEmbeddings.AlmostEmbedding
end

-- Lax263307.InducedRouteEdges
section
namespace Lax263307.InducedRouteEdges
end Lax263307.InducedRouteEdges
end

-- Lax263307.HostRestriction
section
namespace Lax263307.HostRestriction
end Lax263307.HostRestriction
end

-- Lax263307.IsolatedEmbeddingTransfer
section
namespace Lax263307.IsolatedEmbeddingTransfer
end Lax263307.IsolatedEmbeddingTransfer
end

-- Lax263307.EdgeDeletionWidth
section
namespace Lax263307
end Lax263307

namespace Lax263307.EdgeDeletionWidth
end Lax263307.EdgeDeletionWidth
end

-- Lax263307.RoutePruning
section
namespace Lax263307.RoutePruning
end Lax263307.RoutePruning
end

-- Lax263307.RoutingNormalization
section
namespace Lax263307.RoutingNormalization
end Lax263307.RoutingNormalization
end

-- Lax455465.ProductNetwork
section
namespace Lax455465.ProductNetwork.Network
end Lax455465.ProductNetwork.Network

open scoped BigOperators NNReal

namespace Lax455465.ProductNetwork

/-- Whether capacities are shared by both directions of an edge or belong
to individual directed arcs. -/
inductive EdgeKind
  /-- One capacity shared by both directions of an undirected edge. -/
  | undirected
  /-- A separate capacity for each directed arc. -/
  | directed
  deriving DecidableEq

end Lax455465.ProductNetwork
end

-- Lax455465.ConcurrentFlow
section
namespace Lax455465.ConcurrentFlow
end Lax455465.ConcurrentFlow

namespace Lax455465.ConcurrentFlow.edgeLoad
end Lax455465.ConcurrentFlow.edgeLoad
end

-- Lax455465.RationalEncoding
section
namespace Lax455465.RationalEncoding.FlowCertificate
end Lax455465.RationalEncoding.FlowCertificate

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- A product instance with nonnegative rational capacities and weights. -/
structure RationalInstance (n : ℕ) where
  /-- The rational capacity of each edge or directed arc. -/
  capacity : Fin n → Fin n → ℚ≥0
  /-- Loops have zero capacity. -/
  loopless : ∀ v, capacity v v = 0
  /-- The rational weights specifying product demands. -/
  weight : Fin n → ℚ≥0

/-- Encode a nonnegative rational by its canonical numerator and denominator. -/
def encodeRational (q : ℚ≥0) : List ℕ := [q.num, q.den]

/-- Encode the edge model, order, weights, and row-major capacity matrix. -/
def encodeInput {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) : List ℕ :=
  [match kind with | .undirected => 0 | .directed => 1, n] ++
    (List.ofFn I.weight).flatMap encodeRational ++
    (List.ofFn fun u => List.ofFn (I.capacity u)).flatten.flatMap encodeRational

/-- Encode a shore as its length-`n` membership word. -/
def encodeCut {n : ℕ} (S : Finset (Fin n)) : List ℕ :=
  List.ofFn fun v => if v ∈ S then 1 else 0

/-- A polynomial-size rational arc-flow certificate for the ordinary theorem. -/
structure ArcCertificate (n : ℕ) where
  /-- The common demand fraction. -/
  value : ℚ≥0
  /-- The amount assigned to each commodity and directed arc. -/
  arcs : Fin n → Fin n → Fin n → Fin n → ℚ≥0

/-- The value followed by all n⁴ arc coordinates in index order. -/
def encodeArcs {n : ℕ} (certificate : ArcCertificate n) : List ℕ :=
  encodeRational certificate.value ++
    (List.ofFn fun s => List.ofFn fun t => List.ofFn fun u => List.ofFn fun v =>
      encodeRational (certificate.arcs s t u v)).flatten.flatten.flatten.flatten

end Lax455465.RationalEncoding
end

-- Lax455465.FlowCutCertificate
section
open scoped NNReal

namespace Lax455465.FlowCutCertificate

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

/-- The cut and rational path flow returned by a flow–cut algorithm. -/
structure Certificate (n : ℕ) where
  /-- One shore of the cut. -/
  cut : Finset (Fin n)
  /-- A concurrent flow with an explicitly claimed value. -/
  flow : ArcCertificate n

/-- The exact output contains the cut followed by the flow certificate. -/
def encodeCertificate {n : ℕ} (certificate : Certificate n) : List ℕ :=
  encodeCut certificate.cut ++ encodeArcs certificate.flow

end Lax455465.FlowCutCertificate
end

-- Lax455465.RamDirectedUniformFlowCut
section
namespace Lax455465.RamDirectedUniformFlowCut
end Lax455465.RamDirectedUniformFlowCut
end

-- Lax263307.VertexSplitting
section
namespace Lax263307.VertexSplitting

open Lax455465.FlowCutCertificate (Certificate encodeCertificate)

open Lax759944.RamPolytime (RamPolytime)

open scoped NNReal NNRat

open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- The input port of an original vertex. -/
def minus {n : ℕ} (v : Fin n) : Fin (2 * n) :=
  ⟨2 * v.val, Nat.mul_lt_mul_of_pos_left v.isLt (Nat.succ_pos 1)⟩

/-- The output port of an original vertex. -/
def plus {n : ℕ} (v : Fin n) : Fin (2 * n) :=
  ⟨2 * v.val + 1, (Nat.mul_succ 2 v.val).symm.trans_le (Nat.mul_le_mul_left 2 v.isLt)⟩

/-- Forget which of the two ports represents a vertex. -/
def original {n : ℕ} (v : Fin (2 * n)) : Fin n :=
  ⟨v.val / 2, (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr
    (Nat.mul_comm 2 n ▸ v.isLt)⟩

/-- Rational capacities and uniform demands on the split network. -/
def splitInstance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) : RationalInstance (2 * n) where
  capacity u v :=
    if u.val % 2 = 0 ∧ v.val = u.val + 1 then x (original u)
    else if u.val % 2 = 1 ∧ v.val + 1 = u.val then large
    else if u.val % 2 = 1 ∧ v.val % 2 = 0 ∧ G.Adj (original u) (original v) then large
    else 0
  loopless v :=
    (if_neg (fun h => Nat.ne_of_lt (Nat.lt_succ_self v.val) h.2)).trans
      ((if_neg (fun h => Nat.ne_of_gt (Nat.lt_succ_self v.val) h.2)).trans
        (if_neg (fun h => h.2.2.ne rfl)))
  weight _ := 1

/-- Original vertices whose input ports lie inside the split cut. -/
def leftShore {n : ℕ} (U : Finset (Fin (2 * n))) : Finset (Fin n) :=
  Finset.univ.filter fun v => minus v ∈ U

/-- Original vertices whose output ports lie outside the split cut. -/
def rightShore {n : ℕ} (U : Finset (Fin (2 * n))) : Finset (Fin n) :=
  Finset.univ.filter fun v => plus v ∉ U

end Lax263307.VertexSplitting
end

-- Lax263307.SplitPathProjection
section
namespace Lax263307.SplitPathProjection
end Lax263307.SplitPathProjection
end

-- Lax263307.RouteDistributions
section
namespace Lax263307.RouteDistributions
end Lax263307.RouteDistributions

namespace Lax263307.RouteDistributions.Distribution
end Lax263307.RouteDistributions.Distribution
end

-- Lax263307.ConditionalRoutes
section
namespace Lax263307.ConditionalRoutes
end Lax263307.ConditionalRoutes
end

-- Lax263307.FiniteProductSampling
section
namespace Lax263307.FiniteProductSampling
end Lax263307.FiniteProductSampling
end

-- Lax263307.CoupledRouteSampling
section
namespace Lax263307.CoupledRouteSampling
end Lax263307.CoupledRouteSampling
end

-- Lax263307.SamplingOutcomes
section
namespace Lax263307.SamplingOutcomes
end Lax263307.SamplingOutcomes
end

-- Lax263307.CoupledSamplingBounds
section
namespace Lax263307.CoupledSamplingBounds
end Lax263307.CoupledSamplingBounds
end

-- Lax263307.SampledAlmostEmbeddings
section
namespace Lax263307.SampledAlmostEmbeddings
end Lax263307.SampledAlmostEmbeddings
end

-- Lax263307.InducedEmbeddingWidth
section
namespace Lax263307.InducedEmbeddingWidth
end Lax263307.InducedEmbeddingWidth
end

-- Lax263307.PowerBagBounds
section
namespace Lax263307.PowerBagBounds
end Lax263307.PowerBagBounds
end

-- Lax263307.WeightedIndependentSet
section
namespace Lax263307
end Lax263307

namespace Lax263307.WeightedIndependentSet
end Lax263307.WeightedIndependentSet

namespace Lax263307.WeightedIndependentSet.Instance
end Lax263307.WeightedIndependentSet.Instance
end

-- Lax263307.RecursionDepth
section
namespace Lax263307.RecursionDepth
end Lax263307.RecursionDepth

namespace Lax263307.RecursionDepth.depth
end Lax263307.RecursionDepth.depth
end

-- Lax263307.SeparatorDecompositions
section
namespace Lax263307.SeparatorDecompositions
end Lax263307.SeparatorDecompositions
end

-- Lax263307.EdgeBagBounds
section
namespace Lax263307.EdgeBagBounds
end Lax263307.EdgeBagBounds
end

-- Lax263307.CostSamplingObstruction
section
namespace Lax263307.CostSamplingObstruction
end Lax263307.CostSamplingObstruction
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
namespace Lax920634
end Lax920634

namespace Lax920634.SeedSearch
end Lax920634.SeedSearch
end

-- Lax920634.SeedRotation
section
namespace Lax920634.SeedRotation
end Lax920634.SeedRotation

namespace Lax920634.SeedRotation.lazyRotation
end Lax920634.SeedRotation.lazyRotation

namespace Lax920634.SeedRotation.walkAt
end Lax920634.SeedRotation.walkAt

namespace Lax920634.SeedRotation.walkEnd
end Lax920634.SeedRotation.walkEnd
end

-- Lax920634.ZigZagConstruction
section
namespace Lax920634.ZigZagConstruction
end Lax920634.ZigZagConstruction

namespace Lax920634.ZigZagConstruction.rotation
end Lax920634.ZigZagConstruction.rotation
end

-- Lax920634.GraphEncoding
section
namespace Lax920634.GraphEncoding
end Lax920634.GraphEncoding

namespace Lax920634.GraphEncoding.levelAfter
end Lax920634.GraphEncoding.levelAfter
end

-- Lax920634.ConstructionSize
section
namespace Lax920634.ConstructionSize
end Lax920634.ConstructionSize
end

-- Lax920634.ExplicitTreewidth
section
namespace Lax920634.ExplicitTreewidth
end Lax920634.ExplicitTreewidth
end

-- Lax920634.SubcubicConstruction
section
namespace Lax920634.SubcubicConstruction
end Lax920634.SubcubicConstruction
end

-- Lax263307.SourceGraphs
section
namespace Lax263307
end Lax263307

namespace Lax263307.SourceGraphs
end Lax263307.SourceGraphs
end

-- Lax263307.WidthGrowth
section
namespace Lax263307
end Lax263307

namespace Lax263307.WidthGrowth
end Lax263307.WidthGrowth
end

-- Lax263307.NoBoundedLoadRoutes
section
namespace Lax263307.NoBoundedLoadRoutes
end Lax263307.NoBoundedLoadRoutes
end

-- Lax263307.ForcedSeparation
section
namespace Lax263307.ForcedSeparation
end Lax263307.ForcedSeparation
end

-- Lax263307.ComputedSeparators
section
namespace Lax263307.ComputedSeparators

open EdgeSublinearSeparators (IsBalancedSeparator)

open Lax759944.RamPolytime (RamPolytime)

open SeparatorComponents (Partition)

open scoped NNRat

open VertexSplitting Lax455465.RationalEncoding

def decodeCut (n : ℕ) (words : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => words.getD v.val 0 = 1

def label {n : ℕ} (R : Finset (Fin n)) : Fin R.card ↪o Fin n :=
  R.orderEmbOfFin rfl

def restriction {n : ℕ} (G : SimpleGraph (Fin n)) (R : Finset (Fin n)) :
    SimpleGraph (Fin R.card) := G.comap (label R)

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Finset (Fin n)) :
    DecidableRel (restriction G R).Adj := inferInstanceAs (DecidableRel (G.comap (label R)).Adj)

def ratio (B n : ℕ) : ℚ := B * ((Nat.log2 (2 * n) : ℚ) + 1)

def scale (n ℓ k : ℕ) : ℚ := (ℓ : ℚ) * n ^ 2 / (3 * k)

def largeCapacity (B n r ℓ k : ℕ) : ℚ≥0 :=
  (Nat.ceil (ratio B n * (2 * r : ℕ) ^ 2 / scale n ℓ k) + 1 : ℕ)

def orient {n : ℕ} (A B : Finset (Fin n)) : Finset (Fin n) × Finset (Fin n) :=
  if B.card ≤ A.card then (A, B) else (B, A)

def step {n : ℕ} (solve : List ℕ → List ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (B ℓ k : ℕ) (R : Finset (Fin n)) :
    Finset (Fin n) × Finset (Fin n) :=
  let I := splitInstance (restriction G R) (fun v => x (label R v))
    (largeCapacity B n R.card ℓ k)
  let U := decodeCut (2 * R.card) (solve (encodeInput .directed I))
  let shores := orient (leftShore U) (rightShore U)
  (shores.1.image (label R), shores.2.image (label R))

def cuts {n : ℕ} (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n)) :
    ℕ → Finset (Fin n) → List (Finset (Fin n) × Finset (Fin n))
  | 0, _ => []
  | fuel + 1, R =>
    if 3 * R.card ≤ 2 * n then []
    else let s := cut R
      s :: cuts cut fuel (s.1 \ s.2)

def remaining {n : ℕ} (start : Finset (Fin n))
    (cs : List (Finset (Fin n) × Finset (Fin n))) : Finset (Fin n) :=
  if h : cs.length = 0 then start else
    let s := cs.get ⟨cs.length - 1, Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one⟩
    s.1 \ s.2

def pieces {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) :
    Option (Fin cs.length) → Finset (Fin n)
  | none => remaining Finset.univ cs
  | some i => (cs.get i).2 \ (cs.get i).1

open GraphClasses PowerBagBounds

open Entropy RepeatedCutAccounting

end Lax263307.ComputedSeparators
end

-- Lax263307.HeavyRationalConditioning
section
namespace Lax263307.HeavyRationalConditioning

open LinearRelaxation Entropy RationalConditioning HeavyConditioning

def rationalFloor (n p : ℕ) : ℚ := 1 / (2 * (n : ℚ) * p * ((Nat.log2 n : ℚ) + 1))

def HeavyPasses {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Prop :=
  Passes G k p y A ∧ rationalFloor n p ^ r ≤ rationalValue y A

instance {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Decidable (HeavyPasses G k p y A) :=
  inferInstanceAs (Decidable (Passes G k p y A ∧ rationalFloor n p ^ r ≤ rationalValue y A))

def findHeavyConditioning {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) : Option (Finset (Fin n)) :=
  (candidates n r).find? fun A => decide (HeavyPasses G k p y A)

end Lax263307.HeavyRationalConditioning
end

-- Lax263307.NearOracle
section
namespace Lax263307.NearOracle.ChildCorrect
end Lax263307.NearOracle.ChildCorrect

namespace Lax263307.NearOracle.Correct
end Lax263307.NearOracle.Correct

namespace Lax263307.NearOracle

open AlgorithmParameters (level load sparsity)

open ComponentCutEncoding (coefficient evaluate)

open ComputedRounding (collect)

open ComputedSeparators (cuts pieces step)

open HeavyRationalConditioning (findHeavyConditioning)

open scoped NNRat

open LinearRelaxation RationalConditioning

def costs {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n)) (v : Fin n) : ℚ≥0 :=
  ⟨max 0 (rationalValue y (insert v A) / rationalValue y A), le_max_left _ _⟩

def order (q : ℕ) : List (Option (Fin q)) := none :: (List.finRange q).map some

inductive Result (n : ℕ)
  | found (vertices : Finset (Fin n))
  | cut (conditioning vertices : Finset (Fin n)) (bound : ℕ)
  | reject

def run {n : ℕ} (flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (y : RationalVector n (level a K B n D))
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))) : Result n :=
  let p := sparsity a K B n D
  match findHeavyConditioning G k p y with
  | none => .reject
  | some A =>
    let x := costs y A
    let cs := cuts
      (step flow G x B (load B n D) k) n Finset.univ
    let parts := pieces cs
    let c : Option (Fin cs.length) → ℚ := fun i => ∑ v ∈ parts i, (x v : ℚ)
    match collect (order cs.length) parts (1 / D) k c
      (fun i t => child (parts i) t) with
    | .found I => .found I
    | .cut C u => .cut A C u

end Lax263307.NearOracle
end

-- Lax263307.RationalCutBuffer
section
namespace Lax263307.RationalCutBuffer

open BufferedEllipsoid (scale)

open Matrix

def denominator {n : ℕ} (a : Fin n → ℚ) : ℕ := ∏ i, (a i).den

def integerNormal {n : ℕ} (a : Fin n → ℚ) (i : Fin n) : ℤ :=
  (a i).num * (denominator a / (a i).den : ℕ)

end Lax263307.RationalCutBuffer
end

-- Lax109476.CertificateSoundness
section
namespace Lax109476.CertificateSoundness
end Lax109476.CertificateSoundness
end

-- Lax263307.DistanceProjection
section
namespace Lax263307.DistanceProjection

open Lax109476.LinearProgram

/-- The distance LP with one additional variable and two rows per coordinate. -/
def distanceProgram {K : Type} [Ring K] {m n : ℕ} (P : Program K m n) (center : Fin n → K) :
    Program K (m + (n + n)) (n + 1) where
  A := Fin.addCases
    (fun i => Fin.addCases (P.A i) (fun _ => 0))
    (Fin.addCases
      (fun i => Fin.addCases (fun j => if i = j then 1 else 0) (fun _ => -1))
      (fun i => Fin.addCases (fun j => if i = j then -1 else 0) (fun _ => -1)))
  b := Fin.addCases P.b (Fin.addCases center (fun i => -center i))
  c := Fin.addCases (fun _ => 0) (fun _ => -1)

def point {K : Type} {n : ℕ} (z : Fin (n + 1) → K) (j : Fin n) : K := z (Fin.castAdd 1 j)

def distance {K : Type} {n : ℕ} (z : Fin (n + 1) → K) : K := z (Fin.natAdd n (0 : Fin 1))

def oldMultipliers {K : Type} {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin m) : K :=
  dual (Fin.castAdd (n + n) i)

def plusMultipliers {K : Type} {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin n) : K :=
  dual (Fin.natAdd m (Fin.castAdd n i))

def minusMultipliers {K : Type} {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin n) : K :=
  dual (Fin.natAdd m (Fin.natAdd n i))

def normal {K : Type} [Sub K] {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin n) : K :=
  minusMultipliers dual i - plusMultipliers dual i

end Lax263307.DistanceProjection
end

-- Lax263307.RationalProjection
section
namespace Lax263307.RationalProjection.Correct
end Lax263307.RationalProjection.Correct

namespace Lax263307.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates

open DistanceProjection

inductive Outcome (n : ℕ)
  | near (point : Fin n → ℚ)
  | far (normal : Fin n → ℚ) (bound : ℚ)
  | reject

/-- Inspect the actual certificate and compare its distance by exact arithmetic. -/
def classify {m n : ℕ} (P : Program ℚ m n) (ρ : ℚ) :
    Certificate (m + (n + n)) (n + 1) → Outcome n
  | .optimal z dual =>
    if distance z ≤ ρ then .near (point z)
    else .far (normal dual) (dualValue P (oldMultipliers dual))
  | .infeasible _ => .reject
  | .unbounded _ _ => .reject

end Lax263307.RationalProjection
end

-- Lax109476.PolynomialTimeSolver
section
namespace Lax109476.PolynomialTimeSolver
end Lax109476.PolynomialTimeSolver
end

-- Lax263307.RegisteredLP
section
namespace Lax263307.RegisteredLP

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding

def value (sign num den : ℕ) : ℚ :=
  if sign = 1 then -(num : ℚ) / den else (num : ℚ) / den

def rational : List ℕ → Option (ℚ × List ℕ)
  | sign :: num :: den :: rest => some (value sign num den, rest)
  | _ => none

def vector : ℕ → List ℕ → Option (List ℚ × List ℕ)
  | 0, input => some ([], input)
  | n + 1, input => (rational input).bind fun qr =>
      (vector n qr.2).map fun tail => (qr.1 :: tail.1, tail.2)

def vectorFunction (n : ℕ) (input : List ℕ) : Option ((Fin n → ℚ) × List ℕ) :=
  (vector n input).map fun result => (fun i => result.1.getD i.val 0, result.2)

def parse (m n : ℕ) : List ℕ → Option (Certificate m n × List ℕ)
  | 0 :: rest => (vectorFunction n rest).bind fun zr =>
      (vectorFunction m zr.2).map fun yr => (.optimal zr.1 yr.1, yr.2)
  | 1 :: rest => (vectorFunction m rest).map fun yr => (.infeasible yr.1, yr.2)
  | 2 :: rest => (vectorFunction n rest).bind fun zr =>
      (vectorFunction n zr.2).map fun dr => (.unbounded zr.1 dr.1, dr.2)
  | _ => none

def certificate {m n : ℕ} (solve : List ℕ → List ℕ) (P : Program ℚ m n) : Certificate m n :=
  ((parse m n (solve (encodeProgram P))).map Prod.fst).getD (.infeasible 0)

end Lax263307.RegisteredLP
end

-- Lax263307.ProjectedOracle
section
namespace Lax263307.ProjectedOracle.Correct
end Lax263307.ProjectedOracle.Correct

namespace Lax263307.ProjectedOracle.SearchCorrect
end Lax263307.ProjectedOracle.SearchCorrect

namespace Lax263307.ProjectedOracle

open BufferedEllipsoid (scale)

open ComponentCutEncoding (coefficient)

open DistanceProjection (distanceProgram)

open MomentLP (Index decode dimension encode program)

open RationalCutBuffer (integerNormal)

open RationalProjection (classify)

open RegisteredLP (certificate)

open RoundedOracleSearch (Reply rationalNormal)

open LinearRelaxation AlgorithmParameters

def tolerance (a K B n D : ℕ) : ℚ := momentFloor a K B n D / (32 * (n : ℚ)^2 * (D : ℚ)^2)

def raw {N : ℕ} (center : Fin N → ℚ) : Fin N → ℚ := fun i => 4 * (N : ℚ) * center i

def run {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n)))
    (center : Index n (level a K B n D) → ℚ) :
    Reply (dimension n (level a K B n D)) (Finset (Fin n)) :=
  let P := program G k (level a K B n D)
  match classify P (tolerance a K B n D)
    (certificate lp (distanceProgram P (raw center))) with
  | .reject => .reject
  | .far normal _ => .cut (integerNormal normal)
  | .near y =>
    match NearOracle.run flow a K B D G k (decode y) child with
    | .reject => .reject
    | .found I => .found I
    | .cut A C u => .cut (integerNormal
        (rationalNormal (encode (coefficient A C u))))

end Lax263307.ProjectedOracle
end
