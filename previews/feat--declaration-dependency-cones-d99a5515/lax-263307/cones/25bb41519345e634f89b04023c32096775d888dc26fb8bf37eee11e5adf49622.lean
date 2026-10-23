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

axiom optimal_gap {m n : ℕ} (P : Program ℝ m n) (center : Fin n → ℝ)
    (z : Fin (n + 1) → ℝ) (dual : Fin (m + (n + n)) → ℝ)
    (primal : PrimalFeasible (distanceProgram P center) z)
    (dual_feasible : DualFeasible (distanceProgram P center) dual)
    (matching : primalValue (distanceProgram P center) z = dualValue (distanceProgram P center) dual) :
    PrimalFeasible P (point z) ∧ 0 ≤ distance z ∧
      (∀ j, |point z j - center j| ≤ distance z) ∧
      (∑ j, |normal dual j|) ≤ 1 ∧
      (∀ y, PrimalFeasible P y → (∑ j, normal dual j * y j) ≤ dualValue P (oldMultipliers dual)) ∧
      (∑ j, normal dual j * center j) - dualValue P (oldMultipliers dual) = distance z

end Lax263307.DistanceProjection
end
