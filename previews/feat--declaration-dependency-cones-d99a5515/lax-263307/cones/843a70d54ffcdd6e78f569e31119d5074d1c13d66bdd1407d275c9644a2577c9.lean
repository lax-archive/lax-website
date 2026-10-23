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
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.DeriveFintype

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

end Lax263307.EdgeSublinearSeparators
end

-- Lax263307.LinearRelaxation
section
namespace Lax263307
end Lax263307

namespace Lax263307.LinearRelaxation
end Lax263307.LinearRelaxation

namespace Lax263307.LinearRelaxation.IsFeasible
end Lax263307.LinearRelaxation.IsFeasible
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

end Lax263307.SeparatorComponents
end

-- Lax263307.BalancedPartitions
section
namespace Lax263307.BalancedPartitions
end Lax263307.BalancedPartitions
end

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
end Lax263307.PathSampling

namespace Lax263307.PathSampling.Distribution
end Lax263307.PathSampling.Distribution
end

-- Lax263307.RepeatedCutAccounting
section
namespace Lax263307.RepeatedCutAccounting

noncomputable def cost {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ v ∈ S, x v

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
namespace Lax228581.Treewidth

/-- A tree decomposition of a simple graph: a finite tree of nodes with a bag
of graph vertices at each node, such that the bags cover every vertex and
every edge, and the nodes whose bags contain any fixed vertex induce a
connected subgraph of the tree. -/
structure TreeDecomposition {V : Type} (G : SimpleGraph V) where
  /-- The node type of the decomposition tree. -/
  Node : Type
  /-- The decomposition tree is finite. -/
  [nodeFintype : Fintype Node]
  /-- The graph on the decomposition nodes. -/
  tree : SimpleGraph Node
  /-- The node graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag assigned to each decomposition node. -/
  bag : Node → Finset V
  /-- Every graph vertex appears in at least one bag. -/
  vertex_mem_bag : ∀ v : V, ∃ i : Node, v ∈ bag i
  /-- Every graph edge has both endpoints together in at least one bag. -/
  edge_mem_bag : ∀ ⦃u v : V⦄, G.Adj u v → ∃ i : Node, u ∈ bag i ∧ v ∈ bag i
  /-- For each graph vertex, the nodes whose bags contain it induce a
  connected subgraph of the tree. -/
  bag_indices_connected :
    ∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected

end Lax228581.Treewidth
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

open GraphClasses InducedEmbeddingWidth Lax228581.Treewidth

def HasPowerBagBound (C : GraphClass) (a A : ℕ) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)), G ∈ C n → ∃ D : TreeDecomposition G,
    ∀ i, (D.bag i).card ^ a ≤ A * (G.edgeSet.ncard + 1) ^ (a - 1)

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

def separator {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) : Finset (Fin n) :=
  cs.foldr (fun s S => (s.1 ∩ s.2) ∪ S) ∅

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

axiom light_separator (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0 < a) (hA : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ (solve : List ℕ → List ℕ) (K B : ℕ), RamPolytime solve ∧
      0 < K ∧ 0 < B ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (x : Fin n → ℚ≥0) (k p ℓ : ℕ),
      0 < k → 0 < p → 0 < ℓ →
      (∀ v, (x v : ℝ) ≤ 1) → (∑ v, (x v : ℝ)) ≤ k →
      edgeCost G (fun v => (x v : ℝ)) ≤ (k : ℝ) ^ 2 / p →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p →
      let cs := cuts (step solve G x B ℓ k) n Finset.univ
      cs.length ≤ n ∧
        IsBalancedSeparator G
          (ComputedSeparators.separator cs) ∧
        cost (fun v => (x v : ℝ)) (ComputedSeparators.separator cs) ≤
          12 * (ratio B n : ℝ) * k / ℓ ∧
        ∃ P : Partition G
            (ComputedSeparators.separator cs) (Option (Fin cs.length)),
          (∀ i, P.vertices i = pieces cs i) ∧ ∀ i, 3 * (P.vertices i).card ≤ 2 * n

end Lax263307.ComputedSeparators
end
