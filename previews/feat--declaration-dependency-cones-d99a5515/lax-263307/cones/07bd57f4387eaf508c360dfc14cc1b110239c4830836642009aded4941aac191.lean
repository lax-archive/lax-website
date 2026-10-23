-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
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

/-- One component of the transposed matrix applied to a dual point. -/
def columnValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (y : Fin m → K) (j : Fin n) : K :=
  ∑ i, P.A i j * y i

/-- The primal objective value. -/
def primalValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (x : Fin n → K) : K :=
  ∑ j, P.c j * x j

/-- The dual objective value. -/
def dualValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (y : Fin m → K) : K :=
  ∑ i, P.b i * y i

/-- A nonnegative primal point satisfies all row upper bounds. -/
def PrimalFeasible {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (x : Fin n → K) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i, rowValue P x i ≤ P.b i

/-- A nonnegative dual point dominates every objective coefficient. -/
def DualFeasible {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (y : Fin m → K) : Prop :=
  (∀ i, 0 ≤ y i) ∧ ∀ j, P.c j ≤ columnValue P y j

/-- The real primal feasible set is nonempty. -/
def IsFeasible {m n : ℕ} (P : Program ℝ m n) : Prop :=
  ∃ x, PrimalFeasible P x

end Lax109476.LinearProgram
end

-- Lax109476.FarkasCertificate
section
namespace Lax109476.FarkasCertificate

open Lax109476.LinearProgram

/-- Nonnegative row multipliers certify an impossible negative upper bound. -/
def IsInfeasibilityCertificate {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (y : Fin m → K) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ columnValue P y j) ∧ dualValue P y < 0

end Lax109476.FarkasCertificate
end

-- Lax109476.RecessionDirection
section
namespace Lax109476.RecessionDirection

open Lax109476.LinearProgram

/-- A nonnegative direction preserves every upper constraint and improves
the maximized objective. -/
def IsImprovingDirection {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (d : Fin n → K) : Prop :=
  (∀ j, 0 ≤ d j) ∧ (∀ i, rowValue P d i ≤ 0) ∧ 0 < primalValue P d

end Lax109476.RecessionDirection
end

-- Lax109476.RationalCertificates
section
namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

/-- Interpret rational coefficient data as a real linear program. -/
def toReal {m n : ℕ} (P : Program ℚ m n) : Program ℝ m n where
  A i j := P.A i j
  b i := P.b i
  c j := P.c j

/-- The exact real interpretation of a rational vector. -/
def realVector {n : ℕ} (x : Fin n → ℚ) : Fin n → ℝ := fun j => x j

/-- A rational certificate for one of the three possible LP outcomes. -/
inductive Certificate (m n : ℕ)
  /-- Primal and dual points with matching objectives. -/
  | optimal (x : Fin n → ℚ) (y : Fin m → ℚ)
  /-- Separating nonnegative multipliers for an infeasible primal system. -/
  | infeasible (y : Fin m → ℚ)
  /-- A feasible base point and an improving recession direction. -/
  | unbounded (x d : Fin n → ℚ)

/-- The exact rational inequalities and equalities validating a certificate. -/
def IsValidCertificate {m n : ℕ} (P : Program ℚ m n) : Certificate m n → Prop
  | .optimal x y => PrimalFeasible P x ∧ DualFeasible P y ∧ primalValue P x = dualValue P y
  | .infeasible y => IsInfeasibilityCertificate P y
  | .unbounded x d => PrimalFeasible P x ∧ IsImprovingDirection P d

end Lax109476.RationalCertificates
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

def Correct {m n : ℕ} (P : Program ℚ m n) (center : Fin n → ℚ) (ρ : ℚ) :
    Outcome n → Prop
  | .near y => PrimalFeasible (toReal P) (realVector y) ∧
      ∀ j, |(y j : ℝ) - (center j : ℝ)| ≤ (ρ : ℝ)
  | .far a α => (∑ j, |(a j : ℝ)|) ≤ 1 ∧
      (∀ y, PrimalFeasible (toReal P) y → (∑ j, (a j : ℝ) * y j) ≤ (α : ℝ)) ∧
      (ρ : ℝ) < (∑ j, (a j : ℝ) * (center j : ℝ)) - (α : ℝ)
  | .reject => ¬ IsFeasible (toReal P)

axiom classify_correct {m n : ℕ} (P : Program ℚ m n) (center : Fin n → ℚ) (ρ : ℚ)
    (certificate : Certificate (m + (n + n)) (n + 1))
    (valid : IsValidCertificate (distanceProgram P center) certificate) :
    Correct P center ρ (classify P ρ certificate)

end Lax263307.RationalProjection
end
