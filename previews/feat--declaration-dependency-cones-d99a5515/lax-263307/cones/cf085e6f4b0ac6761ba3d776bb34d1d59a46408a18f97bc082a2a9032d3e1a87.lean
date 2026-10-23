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
namespace Lax263307
end Lax263307

namespace Lax263307.Entropy
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
namespace Lax455465
end Lax455465

namespace Lax455465.ProductNetwork
end Lax455465.ProductNetwork

namespace Lax455465.ProductNetwork.EdgeKind
end Lax455465.ProductNetwork.EdgeKind

namespace Lax455465.ProductNetwork.Network
end Lax455465.ProductNetwork.Network

namespace Lax455465.ProductNetwork.EdgeKind.directed
end Lax455465.ProductNetwork.EdgeKind.directed

namespace Lax455465.ProductNetwork.EdgeKind.undirected
end Lax455465.ProductNetwork.EdgeKind.undirected
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
namespace Lax455465.RationalEncoding
end Lax455465.RationalEncoding

namespace Lax455465.RationalEncoding.ArcCertificate
end Lax455465.RationalEncoding.ArcCertificate

namespace Lax455465.RationalEncoding.FlowCertificate
end Lax455465.RationalEncoding.FlowCertificate

namespace Lax455465.RationalEncoding.RationalInstance
end Lax455465.RationalEncoding.RationalInstance

namespace Lax455465.RationalEncoding.encodeInput
end Lax455465.RationalEncoding.encodeInput
end

-- Lax455465.FlowCutCertificate
section
namespace Lax455465.FlowCutCertificate
end Lax455465.FlowCutCertificate

namespace Lax455465.FlowCutCertificate.Certificate
end Lax455465.FlowCutCertificate.Certificate
end

-- Lax455465.RamDirectedUniformFlowCut
section
namespace Lax455465.RamDirectedUniformFlowCut
end Lax455465.RamDirectedUniformFlowCut
end

-- Lax263307.VertexSplitting
section
namespace Lax263307
end Lax263307

namespace Lax263307.VertexSplitting
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
namespace Lax263307.ComputedSeparators.cuts
end Lax263307.ComputedSeparators.cuts

namespace Lax263307.ComputedSeparators.pieces
end Lax263307.ComputedSeparators.pieces

namespace Lax263307.ComputedSeparators

open EdgeSublinearSeparators (IsBalancedSeparator)

open Lax759944.RamPolytime (RamPolytime)

open SeparatorComponents (Partition)

open scoped NNRat

open VertexSplitting Lax455465.RationalEncoding

def ratio (B n : ℕ) : ℚ := B * ((Nat.log2 (2 * n) : ℚ) + 1)

open GraphClasses PowerBagBounds

open Entropy RepeatedCutAccounting

end Lax263307.ComputedSeparators
end
