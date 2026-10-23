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

/-- The indicator encoding of a vertex set. -/
def indicator {n : ℕ} (r : ℕ) (I : Finset (Fin n)) : MomentVector n r :=
  fun A => if A.val ⊆ I then 1 else 0

/-- The convex hull of encodings of size-`k` independent sets. -/
def independentSetHull {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ) :
    Set (MomentVector n r) :=
  convexHull ℝ {y | ∃ I : Finset (Fin n),
    G.IsIndepSet (I : Set (Fin n)) ∧ I.card = k ∧ y = indicator r I}

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
namespace Lax808846
end Lax808846

namespace Lax808846.Ram
end Lax808846.Ram

namespace Lax808846.Ram.Instr
end Lax808846.Ram.Instr

namespace Lax808846.Ram.State
end Lax808846.Ram.State

namespace Lax808846.Ram.run
end Lax808846.Ram.run

namespace Lax808846.Ram.Instr.add
end Lax808846.Ram.Instr.add

namespace Lax808846.Ram.Instr.and
end Lax808846.Ram.Instr.and

namespace Lax808846.Ram.Instr.div
end Lax808846.Ram.Instr.div

namespace Lax808846.Ram.Instr.effect
end Lax808846.Ram.Instr.effect

namespace Lax808846.Ram.Instr.halt
end Lax808846.Ram.Instr.halt

namespace Lax808846.Ram.Instr.inputLength
end Lax808846.Ram.Instr.inputLength

namespace Lax808846.Ram.Instr.inputLoad
end Lax808846.Ram.Instr.inputLoad

namespace Lax808846.Ram.Instr.jeof
end Lax808846.Ram.Instr.jeof

namespace Lax808846.Ram.Instr.jump
end Lax808846.Ram.Instr.jump

namespace Lax808846.Ram.Instr.jzero
end Lax808846.Ram.Instr.jzero

namespace Lax808846.Ram.Instr.load
end Lax808846.Ram.Instr.load

namespace Lax808846.Ram.Instr.mul
end Lax808846.Ram.Instr.mul

namespace Lax808846.Ram.Instr.not
end Lax808846.Ram.Instr.not

namespace Lax808846.Ram.Instr.read
end Lax808846.Ram.Instr.read

namespace Lax808846.Ram.Instr.set
end Lax808846.Ram.Instr.set

namespace Lax808846.Ram.Instr.shiftl
end Lax808846.Ram.Instr.shiftl

namespace Lax808846.Ram.Instr.store
end Lax808846.Ram.Instr.store

namespace Lax808846.Ram.Instr.sub
end Lax808846.Ram.Instr.sub

namespace Lax808846.Ram.Instr.write
end Lax808846.Ram.Instr.write
end

-- Lax759944.RamPolytime
section
namespace Lax759944.RamPolytime
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

def radiusDenominator (a K B n D : ℕ) : ℕ :=
  256 * dimension n (level a K B n D) * n ^ 2 * D ^ 2 *
    floorDenominator a K B n D ^ level a K B n D

def precision (a K B n D : ℕ) : ℕ := radiusDenominator a K B n D + 2

end Lax263307.AlgorithmParameters
end

-- Lax263307.SeparatorComponents
section
namespace Lax263307.SeparatorComponents
end Lax263307.SeparatorComponents

namespace Lax263307.SeparatorComponents.Partition
end Lax263307.SeparatorComponents.Partition
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
namespace Lax263307.ComputedRounding
end Lax263307.ComputedRounding

namespace Lax263307.ComputedRounding.Result
end Lax263307.ComputedRounding.Result

namespace Lax263307.ComputedRounding.collect
end Lax263307.ComputedRounding.collect

namespace Lax263307.ComputedRounding.collect_correct
end Lax263307.ComputedRounding.collect_correct

namespace Lax263307.ComputedRounding.Result.cut
end Lax263307.ComputedRounding.Result.cut

namespace Lax263307.ComputedRounding.Result.found
end Lax263307.ComputedRounding.Result.found
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
namespace Lax263307.ComputedSeparators
end Lax263307.ComputedSeparators

namespace Lax263307.ComputedSeparators.cuts
end Lax263307.ComputedSeparators.cuts

namespace Lax263307.ComputedSeparators.pieces
end Lax263307.ComputedSeparators.pieces
end

-- Lax263307.HeavyRationalConditioning
section
namespace Lax263307.HeavyRationalConditioning
end Lax263307.HeavyRationalConditioning
end

-- Lax263307.NearOracle
section
namespace Lax263307.NearOracle
end Lax263307.NearOracle

namespace Lax263307.NearOracle.ChildCorrect
end Lax263307.NearOracle.ChildCorrect

namespace Lax263307.NearOracle.Correct
end Lax263307.NearOracle.Correct

namespace Lax263307.NearOracle.Result
end Lax263307.NearOracle.Result

namespace Lax263307.NearOracle.run
end Lax263307.NearOracle.run

namespace Lax263307.NearOracle.Result.cut
end Lax263307.NearOracle.Result.cut

namespace Lax263307.NearOracle.Result.found
end Lax263307.NearOracle.Result.found

namespace Lax263307.NearOracle.Result.reject
end Lax263307.NearOracle.Result.reject
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
namespace Lax263307.ProjectedOracle.SearchCorrect
end Lax263307.ProjectedOracle.SearchCorrect

namespace Lax263307.ProjectedOracle.run
end Lax263307.ProjectedOracle.run

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

def Good {n : ℕ} (G : SimpleGraph (Fin n)) (k h D : ℕ) (I : Finset (Fin n)) : Prop :=
  G.IsIndepSet (I : Set (Fin n)) ∧ (1 - 4 * (1 / (D : ℝ))) ^ (h+1) * (k : ℝ) ≤ I.card

def Correct {n : ℕ} (G : SimpleGraph (Fin n)) (k h a K B D : ℕ)
    (center : Index n (level a K B n D) → ℚ) :
    Reply (dimension n (level a K B n D)) (Finset (Fin n)) → Prop
  | .found I => Good G k h D I
  | .reject => independentSetHull G k (level a K B n D) = ∅
  | .cut normal => (∃ i, normal i ≠ 0) ∧
    ∀ z ∈ independentSetHull G k (level a K B n D),
    ∀ e : Index n (level a K B n D) → ℝ,
    (∀ i, |e i| ≤ ((2 : ℝ) ^ precision a K B n D)⁻¹) →
      (fun i => (normal i : ℝ)) ⬝ᵥ
        (scale (encode z) + e - (fun i => (center i : ℝ))) ≤ 0

end Lax263307.ProjectedOracle
end
