-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype

-- Lax263307.Entropy
section
namespace Lax263307.Entropy

/-- Entropy measured with natural logarithms. -/
noncomputable def naturalEntropy {n : ℕ} (π : Fin n → ℝ) : ℝ :=
  ∑ v, Real.negMulLog (π v)

/-- Shannon entropy in bits. -/
noncomputable def entropy {n : ℕ} (π : Fin n → ℝ) : ℝ :=
  naturalEntropy π / Real.log 2

/-- Total product probability of ordered adjacent vertex pairs. -/
noncomputable def adjacencyMass {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (π : Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if G.Adj u v then π u * π v else 0

/-- Sum of endpoint-cost products over unordered edges. -/
noncomputable def edgeCost {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (x : Fin n → ℝ) : ℝ :=
  adjacencyMass G x / 2

end Lax263307.Entropy
end

-- Lax263307.PathSampling
section
namespace Lax263307.PathSampling

open Entropy (adjacencyMass edgeCost)

/-- Finite outcome probabilities and their associated vertex sets. -/
structure Distribution (n q : ℕ) where
  /-- Probability of each outcome. -/
  probability : Fin q → ℝ
  /-- Probabilities are nonnegative. -/
  nonnegative : ∀ i, 0 ≤ probability i
  /-- Total probability is one. -/
  normalized : (∑ i, probability i) = 1
  /-- The vertices used by each outcome. -/
  vertices : Fin q → Finset (Fin n)

/-- Probability of using a particular vertex. -/
noncomputable def load {n q : ℕ} (P : Distribution n q) (v : Fin n) : ℝ :=
  ∑ i, if v ∈ P.vertices i then P.probability i else 0

end Lax263307.PathSampling
end

-- Lax263307.RoutingNormalization
section
namespace Lax263307.RoutingNormalization
end Lax263307.RoutingNormalization
end

-- Lax455465.ProductNetwork
section
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

/-- A finite loopless network with nonnegative capacities. -/
structure Network (n : ℕ) where
  /-- The capacity of an edge or arc, with zero denoting absence. -/
  capacity : Fin n → Fin n → ℝ≥0
  /-- Loops are absent. -/
  loopless : ∀ v, capacity v v = 0

/-- The nonnegative weights whose products specify the demands. -/
abbrev VertexWeight (n : ℕ) := Fin n → ℝ≥0

end Lax455465.ProductNetwork
end

-- Lax455465.ConcurrentFlow
section
open scoped BigOperators NNReal

namespace Lax455465.ConcurrentFlow

open Lax455465.ProductNetwork

/-- A finite assignment of nonnegative flow amounts to vertex lists. -/
abbrev PathFlow (n : ℕ) := List (Fin n) →₀ ℝ≥0

/-- The forward load on an arc, counting its occurrences on each path. -/
noncomputable def arcLoad {n : ℕ} (F : PathFlow n) (u v : Fin n) : ℝ≥0 :=
  ∑ P ∈ F.support, F P * ((P.zip P.tail).count (u, v) : ℝ≥0)

/-- The capacity consumed by a path flow in the chosen edge model. -/
noncomputable def edgeLoad {n : ℕ} (kind : EdgeKind) (F : PathFlow n)
    (u v : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => arcLoad F u v + arcLoad F v u
  | .directed => arcLoad F u v

/-- The demand assigned to an ordered pair of distinct endpoints. -/
noncomputable def pairDemand {n : ℕ} (kind : EdgeKind) (π : VertexWeight n)
    (s t : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => π s * π t / 2
  | .directed => π s * π t

/-- An arc flow records a nonnegative amount for each commodity and arc. -/
abbrev ArcFlow (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ≥0

/-- Aggregate forward capacity consumption in the edge formulation. -/
def totalArcLoad {n : ℕ} (F : ArcFlow n) (u v : Fin n) : ℝ≥0 :=
  ∑ s, ∑ t, F s t u v

/-- Shared or separate capacities in the edge formulation. -/
def totalEdgeLoad {n : ℕ} (kind : EdgeKind) (F : ArcFlow n) (u v : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => totalArcLoad F u v + totalArcLoad F v u
  | .directed => totalArcLoad F u v

/-- Net required supply at a vertex for one commodity; diagonal commodities
have zero supply at every vertex. -/
noncomputable def requiredSupply {n : ℕ} (kind : EdgeKind) (π : VertexWeight n)
    (f : ℝ≥0) (s t u : Fin n) : ℝ :=
  if s = t then 0 else
    (if u = s then (f * pairDemand kind π s t : ℝ≥0) else 0) -
    (if u = t then (f * pairDemand kind π s t : ℝ≥0) else 0)

/-- Capacity and exact commodity conservation in the polynomial-size arc formulation. -/
def IsArcConcurrentFlow {n : ℕ} (kind : EdgeKind) (N : Network n)
    (π : VertexWeight n) (f : ℝ≥0) (F : ArcFlow n) : Prop :=
  (∀ u v, totalEdgeLoad kind F u v ≤ N.capacity u v) ∧
  ∀ s t u, (∑ v, (F s t u v : ℝ)) - (∑ v, (F s t v u : ℝ)) =
    requiredSupply kind π f s t u

end Lax455465.ConcurrentFlow
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

-- Lax455465.RationalEncoding
section
namespace Lax455465.RationalEncoding.FlowCertificate
end Lax455465.RationalEncoding.FlowCertificate

namespace Lax455465.RationalEncoding.encodeInput
end Lax455465.RationalEncoding.encodeInput

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

/-- Interpret rational capacities as exact nonnegative real capacities. -/
def RationalInstance.network {n : ℕ} (I : RationalInstance n) : Network n where
  capacity u v := (I.capacity u v : ℝ≥0)
  loopless v := by simpa using congrArg (fun q : ℚ≥0 => (q : ℝ≥0)) (I.loopless v)

/-- Interpret rational vertex weights as exact nonnegative real weights. -/
def RationalInstance.weights {n : ℕ} (I : RationalInstance n) : VertexWeight n :=
  fun v => (I.weight v : ℝ≥0)

/-- Encode a nonnegative rational by its canonical numerator and denominator. -/
def encodeRational (q : ℚ≥0) : List ℕ := [q.num, q.den]

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

open PathSampling (load)

open scoped NNReal NNRat

open RoutingNormalization VertexSplitting

open Lax455465.ConcurrentFlow

structure Distribution {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) where
  probability : Fin q → ℝ
  nonnegative : ∀ i, 0 ≤ probability i
  normalized : (∑ i, probability i) = 1
  route : Fin q → List (Fin n)
  valid : ∀ i, 0 < probability i → (route i).Nodup ∧ (route i).IsChain G.Adj ∧ route i ≠ []
  uniform : ∀ u v, (∑ i, if (route i).head? = some u ∧ (route i).getLast? = some v then
    probability i else 0) = 1 / (n : ℝ) ^ 2

noncomputable def Distribution.toSampling {n q : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) : PathSampling.Distribution n q where
  probability := D.probability
  nonnegative := D.nonnegative
  normalized := D.normalized
  vertices i := (D.route i).toFinset

/-- A high-value split arc-flow certificate yields a bounded-load route distribution. -/
axiom split_arc_distribution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 0 < n) (x : Fin n → ℚ≥0) (large : ℚ≥0) (γ : ℝ) (γ_positive : 0 < γ)
    (f : ℝ≥0) (high : 1 / γ ≤ (f : ℝ)) (F : ArcFlow (2 * n))
    (feasible : IsArcConcurrentFlow .directed (splitInstance G x large).network
      (splitInstance G x large).weights f F) :
    ∃ q, ∃ D : Distribution G q, ∀ z,
      load D.toSampling z ≤ γ * (x z : ℝ) / (n : ℝ) ^ 2

end Lax263307.RouteDistributions
end
