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

open Lax109476.LinearProgram

/-- Nonnegative row multipliers certify an impossible negative upper bound. -/
def IsInfeasibilityCertificate {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (y : Fin m → K) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ columnValue P y j) ∧ dualValue P y < 0

end Lax109476.FarkasCertificate
end

-- Lax109476.FarkasSoundness
section
namespace Lax109476.FarkasSoundness
end Lax109476.FarkasSoundness
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

-- Lax109476.RationalFeasibility
section
namespace Lax109476.RationalFeasibility
end Lax109476.RationalFeasibility
end

-- Lax109476.FarkasLemma
section
namespace Lax109476.FarkasLemma
end Lax109476.FarkasLemma
end

-- Lax109476.WeakDuality
section
namespace Lax109476.WeakDuality
end Lax109476.WeakDuality
end

-- Lax109476.RecessionExistence
section
namespace Lax109476.RecessionExistence
end Lax109476.RecessionExistence
end

-- Lax109476.StrongDuality
section
namespace Lax109476.StrongDuality
end Lax109476.StrongDuality
end

-- Lax109476.CertificateExistence
section
namespace Lax109476.CertificateExistence

open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- Every rational coefficient input has an exact valid outcome certificate. -/
axiom exists_valid_certificate :
  ∀ (m n : ℕ) (P : Program ℚ m n), ∃ certificate : Certificate m n,
    IsValidCertificate P certificate

end Lax109476.CertificateExistence
end
