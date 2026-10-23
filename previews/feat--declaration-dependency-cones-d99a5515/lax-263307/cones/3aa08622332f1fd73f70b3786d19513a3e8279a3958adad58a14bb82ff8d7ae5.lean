-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
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
namespace Lax109476
end Lax109476

namespace Lax109476.LinearProgram
end Lax109476.LinearProgram

namespace Lax109476.LinearProgram.Program
end Lax109476.LinearProgram.Program
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
namespace Lax109476.RationalCertificates
end Lax109476.RationalCertificates

namespace Lax109476.RationalCertificates.Certificate
end Lax109476.RationalCertificates.Certificate

namespace Lax109476.RationalCertificates.IsValidCertificate
end Lax109476.RationalCertificates.IsValidCertificate

namespace Lax109476.RationalCertificates.Certificate.infeasible
end Lax109476.RationalCertificates.Certificate.infeasible

namespace Lax109476.RationalCertificates.Certificate.optimal
end Lax109476.RationalCertificates.Certificate.optimal

namespace Lax109476.RationalCertificates.Certificate.unbounded
end Lax109476.RationalCertificates.Certificate.unbounded
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

end Lax263307.CoordinateCatalog
end

-- Lax263307.MomentLP
section
namespace Lax263307.MomentLP

open ComponentCutEncoding (evaluate)

open LinearRelaxation CoordinateCatalog

open Lax109476.LinearProgram Lax109476.RationalCertificates

abbrev dimension (n r : ℕ) : ℕ := (catalog n r).length

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
namespace Lax263307.RoundedOracleSearch.Reply
end Lax263307.RoundedOracleSearch.Reply

namespace Lax263307.RoundedOracleSearch.scan
end Lax263307.RoundedOracleSearch.scan

namespace Lax263307.RoundedOracleSearch.selectedNormal
end Lax263307.RoundedOracleSearch.selectedNormal

namespace Lax263307.RoundedOracleSearch.trajectory
end Lax263307.RoundedOracleSearch.trajectory

namespace Lax263307.RoundedOracleSearch.Reply.cut
end Lax263307.RoundedOracleSearch.Reply.cut

namespace Lax263307.RoundedOracleSearch.Reply.found
end Lax263307.RoundedOracleSearch.Reply.found

namespace Lax263307.RoundedOracleSearch.Reply.reject
end Lax263307.RoundedOracleSearch.Reply.reject

namespace Lax263307.RoundedOracleSearch

open BufferedEllipsoid (scale)

open Lax109476.RationalEncoding (encodeRational)

open Lax759944.BinaryWordEncoding (bitSize)

open Matrix

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

axiom conditioning_floor (a K B n D : ℕ) :
    (momentFloor a K B n D : ℝ) =
      probabilityFloor n (sparsity a K B n D) ^ level a K B n D

end Lax263307.AlgorithmParameters
end
