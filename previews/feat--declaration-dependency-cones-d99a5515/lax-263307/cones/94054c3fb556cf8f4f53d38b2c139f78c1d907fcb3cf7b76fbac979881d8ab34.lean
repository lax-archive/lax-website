-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sublists
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

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

/-- The value of one constraint row at a primal point. -/
def rowValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (x : Fin n → K) (i : Fin m) : K :=
  ∑ j, P.A i j * x j

/-- A nonnegative primal point satisfies all row upper bounds. -/
def PrimalFeasible {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (x : Fin n → K) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i, rowValue P x i ≤ P.b i

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

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

/-- Interpret rational coefficient data as a real linear program. -/
def toReal {m n : ℕ} (P : Program ℚ m n) : Program ℝ m n where
  A i j := P.A i j
  b i := P.b i
  c j := P.c j

end Lax109476.RationalCertificates
end

-- Lax263307.LinearRelaxation
section
namespace Lax263307.LinearRelaxation

/-- The coordinate sets of the level-`r` relaxation. -/
abbrev Coordinate (n r : ℕ) := {A : Finset (Fin n) // A.card ≤ r + 2}

/-- A vector with precisely the coordinates used by the relaxation. -/
abbrev MomentVector (n r : ℕ) := Coordinate n r → ℝ

/-- Read a coordinate, returning zero outside the truncated coordinate domain. -/
def value {n r : ℕ} (y : MomentVector n r) (A : Finset (Fin n)) : ℝ :=
  if h : A.card ≤ r + 2 then y ⟨A, h⟩ else 0

/-- The five families of linear constraints defining `R_r(G,k)`. -/
structure IsFeasible {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) : Prop where
  /-- The empty moment is normalized. -/
  normalized : value y ∅ = 1
  /-- Each moment lies in the unit interval. -/
  bounds : ∀ A, 0 ≤ y A ∧ y A ≤ 1
  /-- Adding a vertex cannot increase a moment. -/
  monotone : ∀ A : Finset (Fin n), A.card ≤ r + 1 →
    ∀ v, value y (insert v A) ≤ value y A
  /-- Nonindependent sets have zero moment. -/
  vanishes : ∀ A : Coordinate n r, ¬G.IsIndepSet (A.val : Set (Fin n)) → y A = 0
  /-- The cardinality constraint remains valid after conditioning. -/
  mass : ∀ A : Finset (Fin n), A.card ≤ r + 1 →
    ∑ v : Fin n, value y (insert v A) = (k : ℝ) * value y A

end Lax263307.LinearRelaxation
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

axiom primal_characterization {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (x : Index n r → ℝ) :
    PrimalFeasible (toReal (program G k r)) x ↔ IsFeasible G k r (decode x)

end Lax263307.MomentLP
end
